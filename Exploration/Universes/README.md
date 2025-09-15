Context: re-inventing all sorts of UA constructions. Wanted to have
first-order indexed containers as terms to talk about. We want to write data
that look like 'sensible' first-order terms that use tags. In particular,
did not have what we needed in our universe of discourse to state the equations
we needed. Specifically, building a new theory by extending an old one
(in Estonian mode: indexing over the source, fibering over the target), but
we found that wasn't enough; we were unable to say what it was to *be* a
theory refinement, i.e. what the sub-theory relation was, as opposed to how to
make a particular extension. Very specifically: we were not able to state
equations between terms. We were interested in saying things like 
"this theory has been extended by equations, but those equations are derivable"
which we couldn't.

The technicalities involved were that our models were in a finite universe but
some of our data was in Set (in particular the sorts), which meant that various
internalizing operations were hard.

We really wanted to emphasize the "first order data" message.

This made us really wish for a variety of universes (well below Set 0) full
of concrete, first-order data. But we still want them to be closed under a
variety of operations.

Kit we want:
- decidable equality (of U Data)
- traversals
- enumerations
- differential structure
- more precise information on failure of equality (i.e. reason for)

Kit we 'need' to get there:
- thinnings
- looks like we need 'located' versions of thinning operations and bind
