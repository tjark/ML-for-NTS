# Modal Logics for Nominal Transition Systems

These Isabelle theories formalize a modal logic for nominal transition
systems, as presented in the paper

  *Modal Logics for Nominal Transition Systems*

by Joachim Parrow, Johannes Borgström, Lars-Henrik Eriksson, Ramunas
Gutkovas, and Tjark Weber.

These theories are known to work with
[Isabelle2014](https://isabelle.in.tum.de/)
and the corresponding version of
[Nominal2](https://isabelle.in.tum.de/nominal/download.html).

Assuming both Isabelle2014 and Nominal2 are installed, the theories
may be processed as usual: for instance, in batch mode by executing

  `/path/to/Isabelle2014/bin/isabelle build -d /path/to/Nominal/ -D .

or interactively in Isabelle/jEdit by executing, e.g.,

  `/path/to/Isabelle2014/bin/isabelle jedit -d /path/to/Nominal/ -l Nominal2 Equivalence_Implies_Bisimilarity.thy
