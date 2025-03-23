/*
 * Original Work copyright (c) 2021 Microsoft Research
 * Modified Work copyright (c) 2021 Microsoft Research
 *
 * Original Authors: Deevashwer Rathee, Mayank Rathee
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whome the Software is
 * furnished to do so, subject to the following conditions:
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED,
 * INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR
 * A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
 * OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE
 * OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Modified by Akash Shah
 */
#ifndef BATCHEQUALITY_H__
#define BATCHEQUALITY_H__
#include <cmath>
#include <ctime>
#include <thread>
#include "EzPC/SCI/src/Millionaire/bit-triple-generator.h"
#include "EzPC/SCI/src/OT/emp-ot.h"
#include "EzPC/SCI/src/utils/emp-tool.h"

using namespace sci;
using namespace std;

// BatchEquality 类用于处理批量相等性检查的相关操作，
// 主要用于私有值比较协议（Secure Multiparty Computation, SMC）中的处理。
// 它通过不同的加密和协议步骤，计算输入数据的相等性。
template <typename IO>
class BatchEquality {
 public:
  // 输入输出对象，分别为 Alice 和 Bob 使用的 IO 接口
  IO* io1 = nullptr;
  IO* io2 = nullptr;
  // OT 相关包，分别用于 Alice 和 Bob
  sci::OTPack<IO>*otpack1, *otpack2;
  // TripleGenerator 用于生成三元组（用于安全计算）
  TripleGenerator<IO>*triple_gen1, *triple_gen2;
  // party 为当前方的标识，值为 1 或 2（Alice 或 Bob）
  int party;
  // 其他用于批量相等性检查的参数
  int l, r, log_alpha, beta, beta_pow, batch_size, radixArrSize;
  int num_digits, num_triples_corr, num_triples_std, log_num_digits, num_cmps;
  int num_triples;
  uint8_t mask_beta, mask_r;
  Triple* triples_std;
  uint8_t* leaf_eq;
  uint8_t* digits;
  uint8_t** leaf_ot_messages;

  // 构造函数，初始化相关变量并配置 BatchEquality
  BatchEquality(int party, int bitlength, int log_radix_base, int batch_size, int num_cmps, IO* io1,
                IO* io2, sci::OTPack<IO>* otpack1, sci::OTPack<IO>* otpack2) {
    assert(log_radix_base <= 8);
    assert(bitlength <= 64);
    this->party = party;
    this->l = bitlength;
    this->beta = log_radix_base;
    this->io1 = io1;
    this->otpack1 = otpack1;
    this->io2 = io2;
    this->otpack2 = otpack2;
    this->batch_size = batch_size;
    this->num_cmps = num_cmps;
    this->triple_gen1 = new TripleGenerator<IO>(party, io1, otpack1);
    this->triple_gen2 = new TripleGenerator<IO>(3 - party, io2, otpack2);
    configure();
  }

  // 配置方法，用于初始化一些计算参数
  void configure() {
    this->num_digits = ceil((double)l / beta);
    this->r = l % beta;
    this->log_alpha = sci::bitlen(num_digits) - 1;
    this->log_num_digits = log_alpha + 1;
    this->num_triples = num_digits - 1;
    if (beta == 8)
      this->mask_beta = -1;
    else
      this->mask_beta = (1 << beta) - 1;
    this->mask_r = (1 << r) - 1;
    this->beta_pow = 1 << beta;
    this->triples_std = new Triple((num_triples)*batch_size * num_cmps, true);
  }

  // 析构函数，释放动态分配的内存
  ~BatchEquality() {
    delete triple_gen1;
    delete triple_gen2;
  }

  // 设置叶节点消息，这个方法用于设置数据的叶节点 OT 消息
  // 设置叶节点消息的方法，接收输入数据
  void setLeafMessages(uint64_t* data) {
    // 根据当前方的标识设置 radixArrSize
    if (this->party == sci::ALICE) {
      radixArrSize = batch_size * num_cmps;  // Alice 的情况
    } else {
      radixArrSize = num_cmps;  // Bob 的情况
    }

    // 动态分配内存以存储 digits 和 leaf_eq
    digits = new uint8_t[num_digits * radixArrSize];
    leaf_eq = new uint8_t[num_digits * batch_size * num_cmps];

    // 将数据从 LSB 存储到 MSB
    for (int i = 0; i < num_digits; i++)                                           // 遍历每一位
      for (int j = 0; j < radixArrSize; j++)                                       // 遍历每个数据
        if ((i == num_digits - 1) && (r != 0))                                     // 处理最后一位
          digits[i * radixArrSize + j] = (uint8_t)(data[j] >> i * beta) & mask_r;  // 使用 mask_r
        else
          digits[i * radixArrSize + j] =
              (uint8_t)(data[j] >> i * beta) & mask_beta;  // 使用 mask_beta

    // 如果当前方是 Alice
    if (party == sci::ALICE) {
      // 动态分配内存以存储叶节点 OT 消息
      leaf_ot_messages = new uint8_t*[num_digits * num_cmps];
      for (int i = 0; i < num_digits * num_cmps; i++)
        leaf_ot_messages[i] = new uint8_t[beta_pow];  // 为每个消息分配内存

      // 设置叶节点 OT 消息
      // 设置叶节点 OT 消息
      triple_gen1->prg->random_bool((bool*)leaf_eq,
                                    batch_size * num_digits * num_cmps);  // 生成随机布尔值
      for (int i = 0; i < num_digits; i++) {                              // 遍历每一位
        for (int j = 0; j < num_cmps; j++) {                              // 遍历每个比较
          if (i == (num_digits - 1) && (r > 0)) {                         // 处理最后一位且 r 大于 0
#ifdef WAN_EXEC
            set_leaf_ot_messages(leaf_ot_messages[i * num_cmps + j], digits, beta_pow, leaf_eq, i,
                                 j);  // 设置 OT 消息
#else
            set_leaf_ot_messages(leaf_ot_messages[i * num_cmps + j], digits, 1 << r, leaf_eq, i,
                                 j);  // 设置 OT 消息
#endif
          } else {
            set_leaf_ot_messages(leaf_ot_messages[i * num_cmps + j], digits, beta_pow, leaf_eq, i,
                                 j);  // 设置 OT 消息
          }
        }
      }
    }
  }

  // 计算叶节点 OT（可用于执行安全多方计算中的叶节点交互）
  void computeLeafOTs() {
    if (party == sci::ALICE) {
      // Perform Leaf OTs
      // 执行叶节点 OT
#ifdef WAN_EXEC
      otpack1->kkot_beta->send(leaf_ot_messages, num_cmps * (num_digits), 3);
#else
      if (r == 1) {
        otpack1->kkot_beta->send(leaf_ot_messages, num_cmps * (num_digits - 1), 3);
        otpack1->iknp_straight->send(leaf_ot_messages + num_cmps * (num_digits - 1), num_cmps, 3);
      } else if (r != 0) {
        otpack1->kkot_beta->send(leaf_ot_messages, num_cmps * (num_digits - 1), 3);
        if (r == 2) {
          otpack1->kkot_4->send(leaf_ot_messages + num_cmps * (num_digits - 1), num_cmps, 3);
        } else if (r == 3) {
          otpack1->kkot_8->send(leaf_ot_messages + num_cmps * (num_digits - 1), num_cmps, 3);
        } else if (r == 4) {
          otpack1->kkot_16->send(leaf_ot_messages + num_cmps * (num_digits - 1), num_cmps, 3);
        } else {
          throw std::invalid_argument("Not yet implemented!");
        }
      } else {
        otpack1->kkot_beta->send(leaf_ot_messages, num_cmps * num_digits, 3);
      }
#endif
      // Cleanup
      for (int i = 0; i < num_digits * num_cmps; i++) delete[] leaf_ot_messages[i];
      delete[] leaf_ot_messages;
    } else  // party = sci::BOB
    {       // triple_gen1->generate(3-party, triples_std, _16KKOT_to_4OT);
            //  Perform Leaf OTs
#ifdef WAN_EXEC
      otpack1->kkot_beta->recv(leaf_eq, digits, num_cmps * (num_digits), 3);
#else
      if (r == 1) {
        otpack1->kkot_beta->recv(leaf_eq, digits, num_cmps * (num_digits - 1), 3);
        otpack1->iknp_straight->recv(leaf_eq + num_cmps * (num_digits - 1),
                                     digits + num_cmps * (num_digits - 1), num_cmps, 3);
      } else if (r != 0) {
        otpack1->kkot_beta->recv(leaf_eq, digits, num_cmps * (num_digits - 1), 3);
        if (r == 2) {
          otpack1->kkot_4->recv(leaf_eq + num_cmps * (num_digits - 1),
                                digits + num_cmps * (num_digits - 1), num_cmps, 3);
        } else if (r == 3) {
          otpack1->kkot_8->recv(leaf_eq + num_cmps * (num_digits - 1),
                                digits + num_cmps * (num_digits - 1), num_cmps, 3);
        } else if (r == 4) {
          otpack1->kkot_16->recv(leaf_eq + num_cmps * (num_digits - 1),
                                 digits + num_cmps * (num_digits - 1), num_cmps, 3);
        } else {
          throw std::invalid_argument("Not yet implemented!");
        }
      } else {
        otpack1->kkot_beta->recv(leaf_eq, digits, num_cmps * (num_digits), 3);
      }
#endif

      // Extract equality result from leaf_res_cmp
      for (int i = 0; i < num_digits * num_cmps; i++) {
        for (int j = batch_size - 1; j >= 0; j--) {
          leaf_eq[j * num_digits * num_cmps + i] = (leaf_eq[i] >> j) & 1;
        }
      }
    }

    /*for(int i=0; i<10; i++) {
            for(int j=0;j<batch_size; j++) {
                    std::cout<< (int)leaf_eq[j*num_digits*num_cmps+ i] << " ";
            }
            std::cout<< std::endl;
    }*/
    /*for (int i = 0; i < num_cmps; i++)
            res[i] = leaf_res_cmp[i];
*/
    // Cleanup
    delete[] digits;
  }

  void set_leaf_ot_messages(uint8_t* ot_messages, uint8_t* digits, int N, uint8_t* mask_bytes,
                            int i, int j) {
    for (int k = 0; k < N; k++) {
      ot_messages[k] = 0;
      for (int m = 0; m < batch_size; m++) {
        ot_messages[k] =
            ot_messages[k] | (((digits[i * radixArrSize + j * batch_size + m] == k) ^
                               mask_bytes[m * num_digits * num_cmps + i * num_cmps + j])
                              << m);
      }
    }
  }

  /**************************************************************************************************
   *                         AND computation related functions
   **************************************************************************************************/

  void generate_triples() { triple_gen2->generate(3 - party, triples_std, _16KKOT_to_4OT); }

  /**
   * @brief 遍历并计算 AND 操作
   *
   * 此方法用于结合叶节点的 OT 结果，逐步计算出输入数据的 AND 结果。
   * 它通过多轮的计算，将叶节点的结果合并，最终生成每个比较的结果共享。
   *
   * @param res_shares 存储计算结果的指针
   */
  void traverse_and_compute_ANDs(uint8_t* res_shares) {
    // clock_gettime(CLOCK_MONOTONIC, &start);
    //  Combine leaf OT results in a bottom-up fashion
    int counter_std = 0, old_counter_std = 0;
    int counter_corr = 0, old_counter_corr = 0;
    int counter_combined = 0, old_counter_combined = 0;
    uint8_t* ei = new uint8_t[(num_triples * batch_size * num_cmps) / 8];
    uint8_t* fi = new uint8_t[(num_triples * batch_size * num_cmps) / 8];
    uint8_t* e = new uint8_t[(num_triples * batch_size * num_cmps) / 8];
    uint8_t* f = new uint8_t[(num_triples * batch_size * num_cmps) / 8];

    int old_triple_count = 0, triple_count = 0;

    for (int i = 1; i < num_digits; i *= 2) {
      int counter = 0;
      for (int j = 0; j < num_digits and j + i < num_digits; j += 2 * i) {
        for (int k = 0; k < batch_size; k++) {
          for (int m = 0; m < num_cmps; m += 8) {
            ei[(counter * batch_size * num_cmps + k * num_cmps + m) / 8] =
                triples_std
                    ->ai[(triple_count + counter * batch_size * num_cmps + k * num_cmps + m) / 8];
            fi[(counter * batch_size * num_cmps + k * num_cmps + m) / 8] =
                triples_std
                    ->bi[(triple_count + counter * batch_size * num_cmps + k * num_cmps + m) / 8];
            ei[(counter * batch_size * num_cmps + k * num_cmps + m) / 8] ^=
                sci::bool_to_uint8(leaf_eq + j * num_cmps + k * num_digits * num_cmps + m, 8);
            fi[(counter * batch_size * num_cmps + k * num_cmps + m) / 8] ^=
                sci::bool_to_uint8(leaf_eq + (j + i) * num_cmps + k * num_digits * num_cmps + m, 8);
          }
        }
        counter++;
      }
      triple_count += counter * batch_size * num_cmps;
      int comm_size = (counter * batch_size * num_cmps) / 8;

      if (party == sci::ALICE) {
        io1->send_data(ei, comm_size);
        io1->send_data(fi, comm_size);
        io1->recv_data(e, comm_size);
        io1->recv_data(f, comm_size);
      } else  // party = sci::BOB
      {
        io1->recv_data(e, comm_size);
        io1->recv_data(f, comm_size);
        io1->send_data(ei, comm_size);
        io1->send_data(fi, comm_size);
      }

      for (int i = 0; i < comm_size; i++) {
        e[i] ^= ei[i];
        f[i] ^= fi[i];
      }

      counter = 0;
      for (int j = 0; j < num_digits and j + i < num_digits; j += 2 * i) {
        for (int k = 0; k < batch_size; k++) {
          for (int m = 0; m < num_cmps; m += 8) {
            uint8_t temp_z;
            if (party == sci::ALICE)
              temp_z = e[(counter * batch_size * num_cmps + k * num_cmps + m) / 8] &
                       f[(counter * batch_size * num_cmps + k * num_cmps + m) / 8];
            else
              temp_z = 0;

            temp_z ^=
                f[(counter * batch_size * num_cmps + k * num_cmps + m) / 8] &
                triples_std
                    ->ai[(old_triple_count + counter * batch_size * num_cmps + k * num_cmps + m) /
                         8];
            temp_z ^=
                e[(counter * batch_size * num_cmps + k * num_cmps + m) / 8] &
                triples_std
                    ->bi[(old_triple_count + counter * batch_size * num_cmps + k * num_cmps + m) /
                         8];
            temp_z ^=
                triples_std
                    ->ci[(old_triple_count + counter * batch_size * num_cmps + k * num_cmps + m) /
                         8];
            sci::uint8_to_bool(leaf_eq + j * num_cmps + k * num_digits * num_cmps + m, temp_z, 8);
          }
        }
        counter++;
      }
      old_triple_count = triple_count;
    }

    for (int i = 0; i < num_cmps; i++) {
      res_shares[i] = 0;
      for (int j = 0; j < batch_size; j++) {
        res_shares[i] = res_shares[i] ^ leaf_eq[j * num_digits * num_cmps + i];
      }
    }

    // cleanup
    delete[] ei;
    delete[] fi;
    delete[] e;
    delete[] f;
  }
};

/**
 * @brief 计算叶子OT的线程函数
 *
 * 此函数用于在单独的线程中调用 BatchEquality 类的 computeLeafOTs 方法。
 *
 * @param compare 指向 BatchEquality<NetIO> 对象的指针
 */
void computeLeafOTsThread(BatchEquality<NetIO>* compare) { compare->computeLeafOTs(); }

/**
 * @brief 生成三元组的线程函数
 *
 * 此函数用于在单独的线程中调用 BatchEquality 类的 generate_triples 方法。
 *
 * @param compare 指向 BatchEquality<NetIO> 对象的指针
 */
void generate_triples_thread(BatchEquality<NetIO>* compare) { compare->generate_triples(); }

void perform_batch_equality(uint64_t* inputs, BatchEquality<NetIO>* compare, uint8_t* res_shares) {
  std::thread cmp_threads[2];
  compare->setLeafMessages(inputs);
  cmp_threads[0] = std::thread(computeLeafOTsThread, compare);
  cmp_threads[1] = std::thread(generate_triples_thread, compare);
  for (int i = 0; i < 2; ++i) {
    cmp_threads[i].join();
  }

  compare->traverse_and_compute_ANDs(res_shares);
}

#endif  // BATCHEQUALITY_H__
