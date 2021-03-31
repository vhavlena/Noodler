FROM xblahoud/awalipy:91c3878

MAINTAINER Fanda Blahoudek <fandikb+dev@gmail.com>

USER root

# Copy the main stuff
COPY noodler ${HOME}/noodler
COPY README.md example-full-algo.ipynb example-full-algo-long.ipynb ${HOME}/

# Explanatory notebook
COPY pastry-and-noodles.ipynb ${HOME}/
COPY img ${HOME}/img

RUN chown -R ${NB_UID} ${HOME}
# Switch back to jovyan to avoid accidental container runs as root
USER $NB_UID
