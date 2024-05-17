# PLFA

Notes for https://plfa.github.io/

P.S. If you want to install Agda:

1. Get stack: curl -sSL https://get.haskellstack.org/ | sh
2. append to .bashrc: 'export PATH=$PATH:~/.local/bin
3. source ~/.bashrc 
4. Clone the Agda Github repo
5. cd into it
6. :> stack setup
7. :> stack init
8. :> stack install

If you want to tell Agda where the standard library is:

1. Clone the Agda Standard Library Github repo
2. mkdir -p ~/.agda
3. echo "$HOME/agda-stdlib/standard-library.agda-lib" >> ~/.agda/libraries
4. echo "standard-library" >> ~/.agda/defaults

