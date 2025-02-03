FROM python:bookworm

ARG nproc=32

RUN apt-get update && apt-get upgrade -y
RUN apt-get install -y git cmake build-essential
RUN pip3 install -U pip && pip3 install lark

WORKDIR /root
RUN git clone https://github.com/Z3Prover/z3
ADD patches/new-tactic.patch /root
ADD src/server.py /root/
RUN chmod +x /root/server.py

ENV nproc=${nproc}
WORKDIR /root/z3
RUN git checkout 814d7f4d
RUN git apply /root/new-tactic.patch
RUN mkdir build && cd build && cmake \
  -G "Unix Makefiles" \
  -DCMAKE_BUILD_TYPE=Release \
  -DZ3_BUILD_TEST_EXECUTABLES=OFF \
  -DZ3_INSTALL_PYTHON_BINDINGS=ON \
  -DZ3_BUILD_PYTHON_BINDINGS=ON \
  ..
RUN cd build && make -j${nproc} && make install

CMD ["python3", "-u", "/root/server.py"]