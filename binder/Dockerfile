ARG BASE_CONTAINER=jupyter/base-notebook:aec555e49be6
FROM $BASE_CONTAINER

MAINTAINER Fanda Blahoudek <fandikb+dev@gmail.com>

USER root

RUN apt-get update && apt-get install -y \
  build-essential \
  cmake \
  graphviz \
  libncurses5-dev

# Install Awali
COPY binder/* /tmp/
RUN pip3 install -U cython
RUN cd /tmp && ./install_awali.sh && rm -f install_awali.sh
RUN cd /tmp

# Copy the main stuff
COPY noodler ${HOME}/noodler
COPY README.md example-full-algo.ipynb example-full-algo-long.ipynb ${HOME}/

# Explanatory notebook
COPY pastry-and-noodles.ipynb ${HOME}/
COPY img ${HOME}/img

# Clear the artificial empty directory
RUN rm -r ${HOME}/work

RUN chown -R ${NB_UID} ${HOME}
# Switch back to jovyan to avoid accidental container runs as root
USER $NB_UID
