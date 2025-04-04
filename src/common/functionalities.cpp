// Original Work copyright (c) Oleksandr Tkachenko
// Modified Work copyright (c) 2021 Microsoft Research
//
// \author Oleksandr Tkachenko
// \email tkachenko@encrypto.cs.tu-darmstadt.de
// \organization Cryptography and Privacy Engineering Group (ENCRYPTO)
// \TU Darmstadt, Computer Science department
//
// \copyright The MIT License. Copyright Oleksandr Tkachenko
//
// Permission is hereby granted, free of charge, to any person obtaining
// a copy of this software and associated documentation files (the "Software"),
// to deal in the Software without restriction, including without limitation
// the rights to use, copy, modify, merge, publish, distribute, sublicense,
// and/or sell copies of the Software, and to permit persons to whom the Software
// is furnished to do so, subject to the following conditions:
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED,
// INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR
// A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
// HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
// OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE
// OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
//
// Modified by Akash Shah

#include "functionalities.h"

#include "ENCRYPTO_utils/connection.h"
#include "ENCRYPTO_utils/socket.h"
#include "abycore/sharing/boolsharing.h"
#include "abycore/sharing/sharing.h"
// #include "polynomials/Poly.h"

#include <algorithm>
#include <chrono>
#include <cmath>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <memory>
#include <random>
#include <ratio>
#include <unordered_map>
#include <unordered_set>
#include "HashingTables/common/hash_table_entry.h"
#include "HashingTables/common/hashing.h"
#include "HashingTables/cuckoo_hashing/cuckoo_hashing.h"
#include "HashingTables/simple_hashing/simple_hashing.h"
#include "batch_equality.h"
#include "config.h"
#include "equality.h"
#include "table_opprf.h"

#include <openssl/sha.h>

struct hashlocmap {
  int bin;
  int index;
};

std::vector<uint64_t> content_of_bins;

namespace ENCRYPTO {

using share_ptr = std::shared_ptr<share>;

using milliseconds_ratio = std::ratio<1, 1000>;
using duration_millis = std::chrono::duration<double, milliseconds_ratio>;

void run_psm_1(std::vector<uint64_t> &inputs, uint64_t role, uint64_t bitlen, uint64_t radix,
               sci::NetIO *ioArr[2], std::string address, uint64_t port) {
  //  Server role=0 party = 2 Bob
  //  Client role=1 party = 1 Alice 有一个集合
  std::cout << "role: " << role << std::endl;

  sci::OTPack<sci::NetIO> *otpackArr[2];

  // Config
  int l = (int)bitlen;
  int b = (int)radix;
  int num_cmps, rmdr;
  // rmdr 是 context.nbins 除以 8 的余数。它用于确定在处理输入数据时是否需要填充额外的位
  rmdr = inputs.size() % 8;
  // num_cmps 是 context.nbins 加上 rmdr 的值。它表示在进行比较时的总数量
  num_cmps = inputs.size() + rmdr;

  int pad;
  uint64_t value;

  int party = 1;

  if (role == SERVER) {
    party = 2;
    pad = rmdr;
    value = S_CONST;
    for (int i = 0; i < pad; i++) {
      content_of_bins[inputs.size() + i] = value;
    }
  } else {
    pad = 3 * rmdr;
    value = C_CONST;
    for (int i = 0; i < pad; i++) {
      content_of_bins[3 * inputs.size() + i] = value;
    }
  }

  uint8_t *res_shares = new uint8_t[num_cmps];

  otpackArr[0] = new OTPack<NetIO>(ioArr[0], party, b, l);
  otpackArr[1] = new OTPack<NetIO>(ioArr[1], 3 - party, b, l);

  perform_equality(inputs.data(), party, l, b, num_cmps, address, port, res_shares, ioArr,
                   otpackArr);

  cout << "Writing resultant shares to File ..." << endl;
  ofstream res_file;
  res_file.open("res_share_P" + to_string(role) + ".txt");
  for (int i = 0; i < inputs.size(); i++) {
    // res_file << res_shares[i] << endl;
    res_file << static_cast<int>(inputs[i]) << " " << static_cast<int>(res_shares[i]) << endl;
  }
  res_file.close();

  cout << "finnished." << endl;
}

/**
 * 运行电路PSI。
 *
 * 该函数根据输入的值和上下文信息，执行PSI协议，并记录相关的时间统计信息。
 *
 * 参数:
 * - inputs: 输入的64位无符号整数向量。
 * - context: 包含PSI协议运行所需上下文的PsiAnalyticsContext对象。
 * - sock: 用于通信的CSocket对象的唯一指针。
 * - ioArr: 用于SCI通信的NetIO对象的指针数组。
 * - chl: osuCrypto通道对象。
 */
void run_circuit_psi(const std::vector<std::uint64_t> &inputs, PsiAnalyticsContext &context,
                     std::unique_ptr<CSocket> &sock, sci::NetIO *ioArr[2],
                     osuCrypto::Channel &chl) {
  int party = 1;
  if (context.role == 0) {
    party = 2;
  }

  sci::OTPack<sci::NetIO> *otpackArr[2];

  // Config
  int l = (int)context.bitlen;
  int b = (int)context.radix;

  int num_cmps, rmdr;
  rmdr = context.nbins % 8;
  num_cmps = context.nbins + rmdr;
  int pad;
  uint64_t value;
  if (context.role == 0) {
    pad = rmdr;
    value = S_CONST;
  } else {
    pad = 3 * rmdr;
    value = C_CONST;
  }

  uint8_t *res_shares;

  if (context.role == CLIENT) {
    std::vector<std::vector<uint64_t>> opprf_values(context.nbins,
                                                    std::vector<uint64_t>(context.ffuns));
    const auto clock_time_total_start = std::chrono::system_clock::now();
    content_of_bins.reserve(3 * num_cmps);

    // Hashing Phase
    const auto hashing_start_time = std::chrono::system_clock::now();
    ENCRYPTO::CuckooTable cuckoo_table(static_cast<std::size_t>(context.nbins));
    cuckoo_table.SetNumOfHashFunctions(context.nfuns);
    cuckoo_table.Insert(inputs);
    cuckoo_table.MapElements();

    if (cuckoo_table.GetStashSize() > 0u) {
      std::cerr << "[Error] Stash of size " << cuckoo_table.GetStashSize() << " occured\n";
    }

    auto cuckoo_table_v = cuckoo_table.AsRawVector();
    const auto hashing_end_time = std::chrono::system_clock::now();
    const duration_millis hashing_duration = hashing_end_time - hashing_start_time;
    context.timings.hashing = hashing_duration.count();

    // OPRF Phase
    auto masks_with_dummies = ot_receiver(cuckoo_table_v, chl, context);

    // Hint Computation Phase
    std::vector<uint64_t> garbled_cuckoo_filter;
    garbled_cuckoo_filter.reserve(context.fbins);

    const auto ftrans_start_time = std::chrono::system_clock::now();
    sock->Receive(garbled_cuckoo_filter.data(), context.fbins * sizeof(uint64_t));
    const auto ftrans_end_time = std::chrono::system_clock::now();
    const duration_millis hint_trans = ftrans_end_time - ftrans_start_time;
    context.timings.hint_transmission = hint_trans.count();

    const auto filter_start_time = std::chrono::system_clock::now();

    ENCRYPTO::CuckooTable garbled_cuckoo_table(static_cast<std::size_t>(context.fbins));
    garbled_cuckoo_table.SetNumOfHashFunctions(context.ffuns);
    garbled_cuckoo_table.Insert(cuckoo_table_v);
    auto addresses = garbled_cuckoo_table.GetElementAddresses();

    if (context.psm_type == PsiAnalyticsContext::PSM1) {
      for (int i = 0; i < context.nbins; i++) {
        osuCrypto::PRNG prngo(masks_with_dummies[i], 2);
        for (int j = 0; j < context.ffuns; j++) {
          content_of_bins[i * context.ffuns + j] =
              garbled_cuckoo_filter[addresses[i * context.ffuns + j]] ^ prngo.get<uint64_t>();
        }
      }
    } else {
      for (int i = 0; i < context.nbins; i++) {
        osuCrypto::PRNG prngo(masks_with_dummies[i], 2);
        for (int j = 0; j < context.ffuns; j++) {
          opprf_values[i][j] =
              garbled_cuckoo_filter[addresses[i * context.ffuns + j]] ^ prngo.get<uint64_t>();
        }
      }
    }

    const auto filter_end_time = std::chrono::system_clock::now();
    const duration_millis hint_duration = filter_end_time - filter_start_time;
    context.timings.hint_computation = hint_duration.count();

    res_shares = new uint8_t[num_cmps];
    for (int i = 0; i < pad; i++) {
      content_of_bins[3 * context.nbins + i] = value;
    }

    // PSM Phase
    const auto baseots_start_time = std::chrono::system_clock::now();
    otpackArr[0] = new OTPack<NetIO>(ioArr[0], party, b, l);
    otpackArr[1] = new OTPack<NetIO>(ioArr[1], 3 - party, b, l);
    const auto baseots_end_time = std::chrono::system_clock::now();
    const duration_millis base_ots_duration = baseots_end_time - baseots_start_time;
    context.timings.base_ots_sci = base_ots_duration.count();

    const auto clock_time_cir_start = std::chrono::system_clock::now();
    if (context.psm_type == PsiAnalyticsContext::PSM1) {
      BatchEquality<NetIO> *compare;
      compare = new BatchEquality<NetIO>(party, l, b, 3, num_cmps, ioArr[0], ioArr[1], otpackArr[0],
                                         otpackArr[1]);
      perform_batch_equality(content_of_bins.data(), compare, res_shares);
    } else {
      const int ts = 4;
      auto table_masks = ot_sender(opprf_values, chl, context);
      uint64_t bufferlength = (uint64_t)ceil(context.nbins / 2.0);
      osuCrypto::PRNG tab_prng(osuCrypto::sysRandomSeed(), bufferlength);

      content_of_bins.reserve(num_cmps);
      for (int i = 0; i < context.nbins; i++) {
        content_of_bins[i] = tab_prng.get<uint64_t>();
      }

      std::vector<osuCrypto::block> padding_vals;
      padding_vals.reserve(num_cmps);
      std::vector<uint64_t> table_opprf;
      table_opprf.reserve(ts * num_cmps);
      osuCrypto::PRNG padding_prng(osuCrypto::sysRandomSeed(), 2 * num_cmps);

      bufferlength = (uint64_t)ceil(context.nbins / 2.0);
      osuCrypto::PRNG dummy_prng(osuCrypto::sysRandomSeed(), bufferlength);

      // Get addresses
      uint64_t addresses1[context.ffuns];
      uint8_t bitaddress[context.ffuns];
      uint8_t bitindex[ts];
      uint64_t mask_ad = (1ULL << 2) - 1;

      double ave_ctr = 0.0;

      for (int i = 0; i < context.nbins; i++) {
        bool uniqueMap = false;
        int ctr = 0;
        while (!uniqueMap) {
          auto nonce = padding_prng.get<osuCrypto::block>();

          for (int j = 0; j < context.ffuns; j++) {
            addresses1[j] =
                hashToPosition(reinterpret_cast<uint64_t *>(&table_masks[i][j])[0], nonce);
            bitaddress[j] = addresses1[j] & mask_ad;
          }

          uniqueMap = true;
          for (int j = 0; j < ts; j++) bitindex[j] = ts;

          for (uint8_t j = 0; j < context.ffuns; j++) {
            if (bitindex[bitaddress[j]] != ts) {
              uniqueMap = false;
              break;
            } else {
              bitindex[bitaddress[j]] = j;
            }
          }

          if (uniqueMap) {
            padding_vals.push_back(nonce);
            for (int j = 0; j < ts; j++)
              if (bitindex[j] != -1) {
                table_opprf[i * ts + j] =
                    reinterpret_cast<uint64_t *>(&table_masks[i][bitindex[j]])[0] ^
                    content_of_bins[i];
              } else {
                table_opprf[i * ts + j] = dummy_prng.get<uint64_t>();
              }
            ave_ctr += ctr;
          }
          ctr++;
        }
      }

      ave_ctr = ave_ctr / context.nbins;

      // Send nonces
      sock->Send(padding_vals.data(), context.nbins * sizeof(osuCrypto::block));
      // Send table
      sock->Send(table_opprf.data(), context.nbins * ts * sizeof(uint64_t));

      res_shares = new uint8_t[num_cmps];
      for (int i = 0; i < pad; i++) {
        content_of_bins[context.nbins + i] = value;
      }

      perform_equality(content_of_bins.data(), party, context.bitlen, b, num_cmps, context.address,
                       context.port, res_shares, ioArr, otpackArr);
    }
    const auto clock_time_cir_end = std::chrono::system_clock::now();
    const duration_millis cir_duration = clock_time_cir_end - clock_time_cir_start;
    context.timings.psm_time = cir_duration.count();

    const auto clock_time_total_end = std::chrono::system_clock::now();
    const duration_millis total_duration = clock_time_total_end - clock_time_total_start;
    context.timings.total = total_duration.count();

  } else {  // Server
    content_of_bins.reserve(num_cmps);
    const auto clock_time_total_start = std::chrono::system_clock::now();

    // Hashing Phase
    const auto hashing_start_time = std::chrono::system_clock::now();

    ENCRYPTO::SimpleTable simple_table(static_cast<std::size_t>(context.nbins));
    simple_table.SetNumOfHashFunctions(context.nfuns);
    simple_table.Insert(inputs);
    simple_table.MapElements();
    // simple_table.Print();

    auto simple_table_v = simple_table.AsRaw2DVector();
    const auto hashing_end_time = std::chrono::system_clock::now();
    const duration_millis hashing_duration = hashing_end_time - hashing_start_time;
    context.timings.hashing = hashing_duration.count();

    auto masks = ot_sender(simple_table_v, chl, context);

    // Hint Computation
    const auto filter_start_time = std::chrono::system_clock::now();
    uint64_t bufferlength = (uint64_t)ceil(context.nbins / 2.0);
    osuCrypto::PRNG prng(osuCrypto::sysRandomSeed(), bufferlength);

    for (int i = 0; i < context.nbins; i++) {
      content_of_bins.push_back(prng.get<uint64_t>());
    }

    std::unordered_map<uint64_t, hashlocmap> tloc;
    std::vector<uint64_t> filterinputs;
    for (int i = 0; i < context.nbins; i++) {
      int binsize = simple_table_v[i].size();
      for (int j = 0; j < binsize; j++) {
        tloc[simple_table_v[i][j]].bin = i;
        tloc[simple_table_v[i][j]].index = j;
        filterinputs.push_back(simple_table_v[i][j]);
      }
    }

    ENCRYPTO::CuckooTable cuckoo_table(static_cast<std::size_t>(context.fbins));
    cuckoo_table.SetNumOfHashFunctions(context.ffuns);
    cuckoo_table.Insert(filterinputs);
    cuckoo_table.MapElements();
    // cuckoo_table.Print();

    if (cuckoo_table.GetStashSize() > 0u) {
      std::cerr << "[Error] Stash of size " << cuckoo_table.GetStashSize() << " occured\n";
    }

    std::vector<uint64_t> garbled_cuckoo_filter;
    garbled_cuckoo_filter.reserve(context.fbins);

    bufferlength = (uint64_t)ceil(context.fbins - 3 * context.nbins);
    osuCrypto::PRNG prngo(osuCrypto::sysRandomSeed(), bufferlength);

    for (int i = 0; i < context.fbins; i++) {
      if (!cuckoo_table.hash_table_.at(i).IsEmpty()) {
        uint64_t element = cuckoo_table.hash_table_.at(i).GetElement();
        uint64_t function_id = cuckoo_table.hash_table_.at(i).GetCurrentFunctinId();
        hashlocmap hlm = tloc[element];
        osuCrypto::PRNG prng(masks[hlm.bin][hlm.index], 2);
        uint64_t pad = 0u;
        for (int j = 0; j <= function_id; j++) {
          pad = prng.get<uint64_t>();
        }
        garbled_cuckoo_filter[i] = content_of_bins[hlm.bin] ^ pad;
      } else {
        garbled_cuckoo_filter[i] = prngo.get<uint64_t>();
      }
    }
    const auto filter_end_time = std::chrono::system_clock::now();
    const duration_millis hint_duration = filter_end_time - filter_start_time;
    context.timings.hint_computation = hint_duration.count();

    const auto ftrans_start_time = std::chrono::system_clock::now();
    sock->Send(garbled_cuckoo_filter.data(), context.fbins * sizeof(uint64_t));
    const auto ftrans_end_time = std::chrono::system_clock::now();
    const duration_millis hint_trans = ftrans_end_time - ftrans_start_time;
    context.timings.hint_transmission = hint_trans.count();

    res_shares = new uint8_t[num_cmps];
    for (int i = 0; i < pad; i++) {
      content_of_bins[context.nbins + i] = value;
    }

    const auto baseots_start_time = std::chrono::system_clock::now();
    otpackArr[0] = new OTPack<NetIO>(ioArr[0], party, b, l);
    otpackArr[1] = new OTPack<NetIO>(ioArr[1], 3 - party, b, l);
    const auto baseots_end_time = std::chrono::system_clock::now();
    const duration_millis base_ots_duration = baseots_end_time - baseots_start_time;
    context.timings.base_ots_sci = base_ots_duration.count();

    const auto clock_time_cir_start = std::chrono::system_clock::now();
    if (context.psm_type == PsiAnalyticsContext::PSM1) {
      BatchEquality<NetIO> *compare;
      compare = new BatchEquality<NetIO>(party, l, b, 3, num_cmps, ioArr[0], ioArr[1], otpackArr[0],
                                         otpackArr[1]);
      perform_batch_equality(content_of_bins.data(), compare, res_shares);
    } else {
      const int ts = 4;
      auto masks_with_dummies = ot_receiver(content_of_bins, chl, context);

      std::vector<osuCrypto::block> padding_vals;
      padding_vals.reserve(num_cmps);
      std::vector<uint64_t> table_opprf;
      table_opprf.reserve(ts * num_cmps);

      // Receive nonces
      sock->Receive(padding_vals.data(), context.nbins * sizeof(osuCrypto::block));
      // Receive table
      sock->Receive(table_opprf.data(), context.nbins * ts * sizeof(uint64_t));

      uint64_t addresses1;
      uint8_t bitaddress;
      uint64_t mask_ad = (1ULL << 2) - 1;
      std::vector<uint64_t> actual_contents_of_bins;
      actual_contents_of_bins.reserve(num_cmps);

      for (int i = 0; i < context.nbins; i++) {
        addresses1 = hashToPosition(reinterpret_cast<uint64_t *>(&masks_with_dummies[i])[0],
                                    padding_vals[i]);
        bitaddress = addresses1 & mask_ad;
        actual_contents_of_bins[i] = reinterpret_cast<uint64_t *>(&masks_with_dummies[i])[0] ^
                                     table_opprf[ts * i + bitaddress];
      }

      for (int i = 0; i < pad; i++) {
        actual_contents_of_bins[context.nbins + i] = value;
      }

      // perform_batch_equality(content_of_bins.data(), compare, res_shares);
      res_shares = new uint8_t[num_cmps];
      perform_equality(actual_contents_of_bins.data(), party, context.bitlen, b, num_cmps,
                       context.address, context.port, res_shares, ioArr, otpackArr);
    }
    const auto clock_time_cir_end = std::chrono::system_clock::now();
    const duration_millis cir_duration = clock_time_cir_end - clock_time_cir_start;
    context.timings.psm_time = cir_duration.count();
    const auto clock_time_total_end = std::chrono::system_clock::now();
    const duration_millis total_duration = clock_time_total_end - clock_time_total_start;
    context.timings.total = total_duration.count();
  }

  // Writing resultant shares to file
  cout << "Writing resultant shares to File ..." << endl;
  ofstream res_file;
  res_file.open("res_share_P" + to_string(context.role) + ".txt");
  for (int i = 0; i < context.nbins; i++) {
    // res_file << res_shares[i] << endl;
    res_file << static_cast<int>(res_shares[i]) << endl;
  }
  res_file.close();
}

/**
 * 建立连接。
 *
 * 根据实体角色（SERVER或CLIENT）建立连接，并返回一个唯一的socket对象指针。
 *
 * 参数:
 * - address: 服务器或客户端的IP地址或域名。
 * - port: 连接的端口号。
 * - role: 实体的角色（SERVER或CLIENT）。
 *
 * 返回:
 * - 一个唯一的socket对象指针，表示已建立的连接。
 */
std::unique_ptr<CSocket> EstablishConnection(const std::string &address, uint16_t port,
                                             e_role role) {
  std::unique_ptr<CSocket> socket;
  if (role == SERVER) {
    socket = Listen(address.c_str(), port);
  } else {
    socket = Connect(address.c_str(), port);
  }
  assert(socket);
  return socket;
}

/**
 * 计算两个64位无符号整数向量的交集大小。
 *
 * 该函数查找两个排序向量v1和v2之间的公共元素，并返回交集的大小。
 *
 * 参数:
 * - v1: 第一个64位无符号整数向量。
 * - v2: 第二个64位无符号整数向量。
 *
 * 返回:
 * - 两个向量之间公共元素的数量。
 */
std::size_t PlainIntersectionSize(std::vector<std::uint64_t> v1, std::vector<std::uint64_t> v2) {
  std::vector<std::uint64_t> intersection_v;

  std::sort(v1.begin(), v1.end());
  std::sort(v2.begin(), v2.end());

  std::set_intersection(v1.begin(), v1.end(), v2.begin(), v2.end(), back_inserter(intersection_v));
  return intersection_v.size();
}

/**
 * 打印时间统计信息。
 *
 * 该函数打印协议各个阶段的计时统计信息，包括哈希、OPRF、提示计算、传输和总运行时间。
 *
 * 参数:
 * - context: 包含时间统计信息的PsiAnalyticsContext对象。
 */
void PrintTimings(const PsiAnalyticsContext &context) {
  std::cout << "Time for hashing " << context.timings.hashing << " ms\n";
  std::cout << "Time for OPRF " << context.timings.oprf << " ms\n";
  std::cout << "Time for hint computation " << context.timings.hint_computation << " ms\n";
  std::cout << "Time for transmission of the hint " << context.timings.hint_transmission << " ms\n";
  std::cout << "Timing for PSM " << context.timings.psm_time << " ms\n";
  std::cout << "Total runtime: " << context.timings.total << "ms\n";
  std::cout << "Total runtime w/o base OTs: "
            << context.timings.total - context.timings.base_ots_sci -
                   context.timings.base_ots_libote
            << "ms\n";
}

/**
 * 重置通信统计信息。
 *
 * 该函数重置与通信相关的各种计数器，为新的执行准备。
 *
 * 参数:
 * - sock: CSocket唯一指针的引用。
 * - chl: osuCrypto通道对象。
 * - ioArr: NetIO对象的指针数组。
 * - context: 包含分析信息的PsiAnalyticsContext对象。
 */
void ResetCommunication(std::unique_ptr<CSocket> &sock, osuCrypto::Channel &chl,
                        sci::NetIO *ioArr[2], PsiAnalyticsContext &context) {
  chl.resetStats();
  sock->ResetSndCnt();
  sock->ResetRcvCnt();
  context.sci_io_start.resize(2);
  for (int i = 0; i < 2; i++) {
    context.sci_io_start[i] = ioArr[i]->counter;
  }
}

/**
 * 累积PSI协议期间的通信统计信息。
 *
 * 该函数收集OPRF、提示传输和SCI（安全计算）通信的通信统计信息，并更新上下文对象，以包含每个阶段的总发送和接收的字节数。
 *
 * 参数:
 * - sock: CSocket唯一指针的引用。
 * - chl: osuCrypto通道对象。
 * - ioArr: NetIO对象的指针数组。
 * - context: 包含分析信息的PsiAnalyticsContext对象。
 */
void AccumulateCommunicationPSI(std::unique_ptr<CSocket> &sock, osuCrypto::Channel &chl,
                                sci::NetIO *ioArr[2], PsiAnalyticsContext &context) {
  context.sentBytesOPRF = chl.getTotalDataSent();
  context.recvBytesOPRF = chl.getTotalDataRecv();

  context.sentBytesHint = sock->getSndCnt();
  context.recvBytesHint = sock->getRcvCnt();

  context.sentBytesSCI = 0;
  context.recvBytesSCI = 0;

  for (int i = 0; i < 2; i++) {
    context.sentBytesSCI += ioArr[i]->counter - context.sci_io_start[i];
  }

  // Send SCI Communication
  if (context.role == CLIENT) {
    sock->Receive(&context.recvBytesSCI, sizeof(uint64_t));
    sock->Send(&context.sentBytesSCI, sizeof(uint64_t));
  } else {
    sock->Send(&context.sentBytesSCI, sizeof(uint64_t));
    sock->Receive(&context.recvBytesSCI, sizeof(uint64_t));
  }
}

/**
 * 打印通信统计信息。
 *
 * 该函数打印通信统计信息，包括OPRF、提示和SCI通信的数据。
 *
 * 参数:
 * - context: 包含通信统计信息的PsiAnalyticsContext对象。
 */
void PrintCommunication(PsiAnalyticsContext &context) {
  context.sentBytes = context.sentBytesOPRF + context.sentBytesHint + context.sentBytesSCI;
  context.recvBytes = context.recvBytesOPRF + context.recvBytesHint + context.recvBytesSCI;
  std::cout << context.role << ": Communication Statistics: " << std::endl;
  double sentinMB, recvinMB;
  sentinMB = context.sentBytesOPRF / ((1.0 * (1ULL << 20)));
  recvinMB = context.recvBytesOPRF / ((1.0 * (1ULL << 20)));
  std::cout << context.role << ": Sent Data OPRF (MB): " << sentinMB << std::endl;
  std::cout << context.role << ": Received Data OPRF (MB): " << recvinMB << std::endl;

  sentinMB = context.sentBytesHint / ((1.0 * (1ULL << 20)));
  recvinMB = context.recvBytesHint / ((1.0 * (1ULL << 20)));
  std::cout << context.role << ": Sent Data Hint (MB): " << sentinMB << std::endl;
  std::cout << context.role << ": Received Data Hint (MB): " << recvinMB << std::endl;

  sentinMB = context.sentBytesSCI / ((1.0 * (1ULL << 20)));
  recvinMB = context.recvBytesSCI / ((1.0 * (1ULL << 20)));
  std::cout << context.role << ": Sent Data CryptFlow2 (MB): " << sentinMB << std::endl;
  std::cout << context.role << ": Received Data CryptFlow2 (MB): " << recvinMB << std::endl;

  sentinMB = context.sentBytes / ((1.0 * (1ULL << 20)));
  recvinMB = context.recvBytes / ((1.0 * (1ULL << 20)));
  std::cout << context.role << ": Total Sent Data (MB): " << sentinMB << std::endl;
  std::cout << context.role << ": Total Received Data (MB): " << recvinMB << std::endl;
}

}  // namespace ENCRYPTO
