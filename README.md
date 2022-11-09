# AutomaticGDH
Automatic tool to attack GDH protocols

## A word of warning:
Most of this code was written during my bachelor internship in 2006...
It is an implementation of the attack considered in : [PerQui06] [On the Impossibility of Building Secure Cliques-type Authenticated Group Key Agreement Protocols](https://perso.uclouvain.be/olivier.pereira/JCS05.pdf)
While i tried to update it, this is really ugly code... but functional

As of today (Nov 2022), it works with current OCaml version (there was some oddities as graphics was removed from the ocaml core suite)

## Use
Assuming a properly installed ocaml, simply run
> ocaml core.ml *filename*

Where filename is the name of your protocol .txt file without the extension.

The program will then run, and output a file filename.txt describing the interaction the attacker should do

## High level idea

GDH protocols are easily protocol.
* There is a generic attack for any protocol with 5+ users.
* It can directly be extended to 4 users, except in 9 cases (depending on who starts, and when they start using some seceets)
For those 9 cases, there are however another possible attacks.
**It should be noted, that those special cases are not the one highlighted in the original paper**
* For 3 cases, it's a mess...
    * There are cases with generic attacks possible
    * Cases where no attacks can be possible
    * And configurations where we could not find criterion. (In this case, the algorithm tries some bruteforce, sometimes finding attacks, sometimes showing there are known, and sometimes giving up because depth/breadth get too high)

## How to describe protocols

Each line contains one flow, of the form
> i - exponent > j

Meaning the user $i$ sends $g^\mathsf{exponent}$ to $j$.
Randomness are expressed as Ri (for example R1), if a user generates several randomness, one can write Ri,k (R1,2) for example.

It is possible for a user having received Ri,k from another to reuse it

One can assume the existence on long term keys between two users Ki|j (the | can be replaced by any non numeral / whitespace symbol). This is done to help parse K123 into K12|3 and K1|23.

Comments can be written on line beginning with %
 
Using ```==EOF== ``` somewhere in the file will end the processing, and allow to include extended comments.

- [ ] Translate the code into english
- [ ] Clean up the code
- [ ] Make a cuter design ...
