{ pkgs ? import <nixpkgs> { } }:

pkgs.mkShell {
  nativeBuildInputs = with pkgs.buildPackages; [
    coq_8_20
    coqPackages_8_20.coqide
    dotnet-sdk_9
  ];
}
