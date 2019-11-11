{ stdenv, llvmPackages, bash, cmake, python, gmp }:

stdenv.mkDerivation rec {
  name = "lean-${version}";
  version = "local";

  # I have way too many untracked files in my checkout
  src = if builtins.pathExists ../.git then builtins.fetchGit { url = ../.; } else ../.;

  nativeBuildInputs = [ bash cmake python ];
  buildInputs = [ gmp llvmPackages.llvm ];
  enableParallelBuilding = true;

  preConfigure = ''
    cd src
  '';
  postConfigure = ''
    patchShebangs ../../bin
  '';

  meta = with stdenv.lib; {
    description = "Automatic and interactive theorem prover";
    homepage    = https://leanprover.github.io/;
    license     = licenses.asl20;
    platforms   = platforms.unix;
  };
}
