{ pkgs ? import <nixpkgs> { } }:

pkgs.mkShell {
  nativeBuildInputs = with pkgs.buildPackages; [
    coq
    coqPackages.coqide
    dotnet-sdk_9
  ];
}
