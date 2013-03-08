*Iliad*
=======

<p align="right">
  <i>
    Rage—Goddess, sing the rage of Peleus' son Achilles,<br/>
    murderous, doomed, that cost the Achaeans countless losses,<br/>
    hurling down to the House of Death so many sturdy souls,<br/>
    great fighters’ souls, but made their bodies carrion,<br/>
    feasts for the dogs and birds,<br/>
    and the will of Zeus was moving toward its end.<br/>
    Begin, Muse, when the two first broke and clashed,<br/>
    Agamemnon lord of men and brilliant Achilles.<br/><br/>
  </i>
  —Homer. The Iliad.
</p>

*Iliad*, the *Implementation of Logical Inference for Adaptive
Devices* is the infrastructure for the *Poem* language.  *Poem* is the
high-level modeling language of the [ASCENS](http://www.ascens-ist.eu)
project.  This implementation is actually Iliad V3; it is based on
Racket and extends Racket with support for non-deterministic
computation, logical reasoning, tuple spaces, and a number of other
useful tools for developing ensembles.  The first two versions were
experimental implementations in Common Lisp and are no longer
developed or supported.

Epeus
-----

<p align="right">
  <i>
  And a powerful, huge man loomed up at once,<br/>
  Panopeus' son Epeus, the famous boxing champion.<br/><br/>
  </i>
  —Homer. The Iliad.
</p>

*Epeus* is the implementation of the object system in Iliad.  (Why is
 this named Epeus?  Well, he was the builder of the Trojan horse,
 which was, however you look at it, a pretty big
 [swindle](http://barzilay.org/Swindle/)).

Odysseus
--------

<p align="right">
  <i>
    But Odysseus, cool tactician, tried to calm him:<br/>
    “Achilles, son of Peleus, greatest of the Achaeans,<br/>
	greater than I, stronger with spears by no small edge—<br/>
	yet I might just surpass you in seasoned judgment<br/>
	by quite a lot, since I have years on you<br/>
	and I know the world much better...<br/><br/>
  </i>
  —Homer. The Iliad.
</p>

*Odysseus* is the implementation of the logical core of the *Poem*
 language.  It will contain the implementation of search strategies,
 backtracking, data structures for clauses and general logical
 formulas and the interface for reasoning services.
 
 
Installation and Execution
--------------------------

TODO: (Essentially, you should just have to download and install the
package using `raco pkg install github://github.com/hoelzl/Iliad` and
be ready to go.  But this is as yet untested.)


The Workflow for the *Iliad* Implementation
-------------------------------------------

<p align="right">
  <i>
    The work done, the feast laid out, they ate well<br/>
    and no man’s hunger lacked a share of the banquet.<br/><br/>
  </i>
  —Homer. The Iliad.
</p>

I used the git-flow branching model for the previous implementations
of *Iliad*.  See the article
"[A successful Git branching model](http://nvie.com/posts/a-successful-git-branching-model/)"
for details.  However, for a small project like Iliad this might be
too heavyweight, so just create a branch, do your development and then
commit.  The `master` branch should always build and run the tests, so
only merge into `master` when your changes are reasonably stable.
Furthermore, I suggest to write the commit messages based on the
[Note About Git Commit Messages](http://tbaggery.com/2008/04/19/a-note-about-git-commit-messages.html)
from tbaggery.


About this Document
-------------------

<p align="right">
  <i>
    No one should ever let such nonsense pass his lips,<br/>
    no one with any skill in fit and proper speech—<br/><br/>
  </i>
  —Homer. The Iliad.
</p>


All quotes from the Iliad are taken from the Penguin Classics edition
translated by Robert Fagles.  The HTML markup for the quotes uses the
old-fashioned ```align="right"``` style, since CSS does currently not
seem to work for the Github renderer.
