FROM rust:latest

RUN apt-get update && apt-get install -y sudo && rm -rf /var/lib/apt/lists/*

# ARG user=makepkg
# ARG uid=1000
# ARG gid=1000
# RUN groupadd -g $gid $user && \
#     useradd -m -u $uid -g $gid -s /bin/bash $user
# RUN apt-get update && apt-get install -y sudo && \
#     echo "$user ALL=(ALL:ALL) NOPASSWD:ALL" > /etc/sudoers.d/$user && \
#     chmod 0440 /etc/sudoers.d/$user
# # RUN useradd --system --create-home $user \
# #     && mkdir -p /etc/sudoers.d \
# #     && echo "$user ALL=(ALL:ALL) NOPASSWD:ALL" > /etc/sudoers.d/$user \
# #     && chmod 0440 /etc/sudoers.d/$user

# RUN mkdir -p /app/results /app/tmp && chown -R $user:$user /app
# WORKDIR /app
# COPY --chown=$user:$user . .
# USER $user

ARG user=makepkg
RUN useradd --system --create-home $user \
  && echo "$user ALL=(ALL:ALL) NOPASSWD:ALL" > /etc/sudoers.d/$user
USER $user
WORKDIR /app
COPY --chown=$user:$user . .
RUN sudo chown -R $user:$user /app
RUN sudo chmod -R a+rwX /app

RUN cargo build --release --features=hotpath,hotpath-alloc
CMD ["/bin/bash"]