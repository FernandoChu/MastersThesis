with (import <nixpkgs> { });
let
  oldPkgs = import
    (builtins.fetchGit {
      # Descriptive name to make the store path easier to identify                
      name = "my-old-revision";
      url = "https://github.com/NixOS/nixpkgs/";
      ref = "refs/heads/nixpkgs-unstable";
      # Search for the revision for the agda versions in
      # https://lazamar.co.uk/nix-versions/?channel=nixpkgs-unstable&package=agda
      rev = "12408341763b8f2f0f0a88001d9650313f6371d5";
    })
    { };
in
mkShell {
  # nativeBuildInputs is usually what you want -- tools you need to run
  buildInputs = [
    oldPkgs.agda
  ];
}

