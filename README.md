# Verified FreeCell
This repository contains a correct-by-construction implementation of the card solitaire game FreeCell that's guaranteed to allow any valid move and disallow any invalid move.

# How to play
The rules are standard [FreeCell](https://en.wikipedia.org/wiki/FreeCell#Rules) - the goal is to move all of the cards to the foundations. The piles (cells/foundations/cascades) are labeled from `0` to `f`; enter a source pile label followed by a space and then a destination pile label (e.g. "5 e") to move a card from one pile to another. Enter "win" to check if you've won, and "quit" to quit.

# How to build
`agda --compile Main.agda` with Agda 2.5.4 or greater. Building requires the Agda standard library to be installed and associated with the name `standard-libarary` in an Agda [`defaults` file](http://agda.readthedocs.io/en/v2.5.3/tools/package-system.html).
