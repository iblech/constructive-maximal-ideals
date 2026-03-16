#!/usr/bin/env bash

# NixOS 23.11: Agda 2.6.4,   stdlib 1.7.3 (not working because map-++ is missing)
# Nixos 24.05: Agda 2.6.4.3, stdlib 2.0
# NixOS 24.11: Agda 2.7.0.1, stdlib 2.1.1
# NixOS 25.05: Agda 2.7.0.1, stdlib 2.2
# NixOS 25.11: Agda 2.8.0,   stdlib 2.3

for i in 24.05 24.11 25.05 25.11; do
  find . -name "*.agdai" -delete
  nix-shell \
    -I nixpkgs=https://nixos.org/channels/nixos-$i/nixexprs.tar.xz \
    -p "agda.withPackages (p: [ p.standard-library ])" \
    --command '
      echo "**********************************"
      echo -n "NixOS '$i': Agda "
      agda --version | grep version | awk "{ print \$3 }" | tr -d "\n"
      echo -n ", stdlib "
      cat $(cat $(which agda) | tr "= " "\n" | grep libraries) | grep standard-library | cut -d- -f4 | cut -d/ -f1
      agda index.agda
      echo
    '
done
