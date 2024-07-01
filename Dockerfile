FROM ubuntu:24.04
RUN apt update && apt -y upgrade

# Install Python and pip
RUN apt install -y python3 pip

# Install OCaml 4.10.0
RUN apt install -y opam
RUN opam init --auto-setup --comp 4.10.0 --disable-sandboxing -y
RUN eval $(opam env)

# Install relevant OCaml libraries
RUN opam install -y dune dune-build-info core menhir

# Clone the guide-type repository from GitHub
WORKDIR /home/
RUN git clone -b subguide_types https://github.com/LongPham7/GuideTypes.git

# Build the program
WORKDIR /home/GuideTypes
RUN eval $(opam env) && make

WORKDIR /home/GuideTypes/bench/type-equality/
CMD ["/bin/bash", "--login"]
