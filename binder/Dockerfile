FROM xblahoud/awalipy:91c3878

MAINTAINER Fanda Blahoudek <fandikb+dev@gmail.com>

USER root

RUN pip install z3-solver

# Copy the main stuff
COPY noodler ${HOME}/noodler

#Copy
COPY README.md example-full-algo.ipynb example-full-algo-long.ipynb ${HOME}/
# Copy graph-based notebooks
COPY notebooks ${HOME}/notebooks
# Copy benchmarks
COPY benchmarks ${HOME}/benchmarks
# Explanatory notebook
COPY pastry-and-noodles.ipynb ${HOME}/
COPY img ${HOME}/img

RUN pip install -e ${HOME}/noodler

RUN chown -R ${NB_UID} ${HOME}

# Switch back to jovyan to avoid accidental container runs as root
USER $NB_UID
