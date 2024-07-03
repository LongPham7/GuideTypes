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

# Copy the guide-type repository to the image
ADD . /home/GuideTypes

# Build the program
WORKDIR /home/GuideTypes
RUN eval $(opam env) && make

# Install relevant Python packages
RUN pip install tabulate --break-system-packages

WORKDIR /home/GuideTypes/bench/type-equality/
CMD ["/bin/bash", "--login"]
