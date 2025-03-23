#!/bin/bash

# 需要安装的包，libboost-all-dev libfmt-dev pkg-config libglib2.0-dev libgmp-dev libssl-dev libntl-dev

cd extern
wget -O boost_1_79_0.tar.gz https://sourceforge.net/projects/boost/files/boost/1.79.0/boost_1_79_0.tar.gz/download
tar xzvf boost_1_79_0.tar.gz
cd boost_1_79_0
./bootstrap.sh --prefix=$(pwd)/boost_install --with-libraries=all
./b2
./b2 install --with=all
cd ..

git clone https://github.com/zhouxv/PSM_C.git
cd PSM_C
mkdir build && cd build
CC=/usr/bin/gcc-9 CXX=/usr/bin/g++-9 cmake ..
cp ../aux_hash/* ../extern/HashingTables/cuckoo_hashing/.
make
