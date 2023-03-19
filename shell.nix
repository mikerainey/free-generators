{ pkgs ? import <nixpkgs> {},
  stdenv ? pkgs.stdenv,
  ghc ? pkgs.ghc,
  stack ? pkgs.stack,
  llvm ? pkgs.llvm
}:

stdenv.mkDerivation rec {
  name = "free-generators-dev";

  buildInputs =
    [ ghc stack llvm ];
  
  # allow architecture-native optimization mode to be used by the C/C++ compiler
  NIX_ENFORCE_NO_NATIVE=0;
}
