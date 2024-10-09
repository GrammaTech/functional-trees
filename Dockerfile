FROM ubuntu:22.04

ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get -y update && \
    apt-get -y install autoconf build-essential git lsof wget \
    python3-pip sbcl curl

# # Install Clozure
RUN mkdir /usr/share/ccl
RUN git clone --depth=1 --branch=v1.12.1 https://github.com/Clozure/ccl.git /usr/share/ccl
RUN curl -L https://github.com/Clozure/ccl/releases/download/v1.12.1/linuxx86.tar.gz \
    | tar xzvf - -C /usr/share/ccl
RUN cd /usr/share/ccl && echo "(ccl:rebuild-ccl :full t)" \
    | ./lx86cl64 --no-init --quiet --batch
RUN echo '#!/bin/sh\n\
    export CCL_DEFAULT_DIRECTORY=/usr/share/ccl\n\
    exec ${CCL_DEFAULT_DIRECTORY}/lx86cl64 "$@"\n\
    ' > /usr/bin/ccl
RUN chmod a+x /usr/bin/ccl

# Build SCBL
RUN rm -rf /root/sbcl && \
    git clone --depth=1 --branch sbcl-2.4.6 https://git.code.sf.net/p/sbcl/sbcl \
    /root/sbcl
RUN cd /root/sbcl && \
    bash make.sh --xc-host='ccl --batch --no-init'\
    --prefix=/usr \
    --with-sb-linkable-runtime --with-sb-dynamic-core \
    --dynamic-space-size=8Gb
RUN apt-get -y remove sbcl
RUN cd /root/sbcl && bash install.sh && sbcl --version

# Install up-to-date ASDF (must be >=3.3.4.8 for package-local nickname support.)
RUN mkdir /root/common-lisp
RUN curl https://gitlab.common-lisp.net/asdf/asdf/-/archive/3.3.7/asdf-3.3.7.tar.gz| tar xzC /root/common-lisp

# Install quicklisp
RUN cd /tmp/ && \
    wget https://beta.quicklisp.org/quicklisp.lisp && \
    sbcl --load quicklisp.lisp \
    --eval '(quicklisp-quickstart:install)'

# Install Python dependencies for readme.py
COPY .cl-make/requirements.txt cl-make-requirements.txt
RUN pip3 install -r cl-make-requirements.txt
# TODO It would be better to do this in cl-make.
RUN pip3 install pytest==7.1.2

WORKDIR /root/quicklisp/local-projects
