# Modal Logics for Nominal Transition Systems

These Isabelle theories formalize a modal logic for nominal transition
systems, as presented in the paper

  *Modal Logics for Nominal Transition Systems*

by Joachim Parrow, Johannes Borgström, Lars-Henrik Eriksson,
Ram&#363;nas Gutkovas, and Tjark Weber.

These theories are known to work with
[Isabelle2016](https://isabelle.in.tum.de/) and the corresponding
version of Nominal2 from the 2016 release of the [Archive of Formal
Proofs](http://afp.sourceforge.net/download.shtml).

Assuming both Isabelle2016 and Nominal2 are installed, the theories
may be processed as usual: for instance, in batch mode by executing

  `/path/to/Isabelle2016/bin/isabelle build -d /path/to/afp-2016-03-02/thys/Nominal2/ -D .`

or interactively in Isabelle/jEdit by executing, e.g.,

  `/path/to/Isabelle2016/bin/isabelle jedit -d /path/to/afp-2016-03-02/thys/Nominal2/ -l Nominal2 Equivalence_Implies_Bisimilarity.thy`
