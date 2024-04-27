# Ideas on Termination of the worklist algorithm

This document elaborates a bit more on some ideas for the termination of the algorithm. 

Firstly, an assumption that I have in what follows is that rules are in a small-step style. 
I think that this makes it easier to formaly state some theorems. I think it is possible to maybe 
formulate things in a big-step style, but this may require some more thought and maybe refactoring.

Secondly there are a few  different, possibly complementary ideas. Maybe not all ideas are useful. 
I wish to talk about 2 things below:

1. First, is a high-level sketch of the proof structure.

2. Secondly, I wish to look closely at the details of measure to some of the partial 
termination results in 1.

## Overall Sketch of the Termination Proof

Sketch of the overall proof idea/structure. We decompose the proof of termination of reduction 
of a worklist, into smaller auxiliary results that cover partial termination results about 
different kinds of entries. Then we combine these results in the overall proof of termination.

Notation:

-->*   means reduce in 0 or more steps.

### Termination of Subtyping Work and Existential variables:

If `WF (T |- A <: B)` then either:
  1. `T |- A <: B` fails to reduce; or 
  2. Exists `T'`, such that `T |- A <: B -->* T'`   where `T'` has one less work/judgement than the original list (but it may increase other things like variables/existentials)

A useful related result if that if we know that `A` and `B` do not contain universals, then 
we actually have a tigher result:

If `WF (T |- A <: B)` and `A` and `B` do not contain universals then either:
  1. `T |- A <: B` fails to reduce; or 
  2. `T |- A <: B` -->* T

This tighter result is useful to prove termination of work introduced by existential variables. 

Note that existential variables work is basically reduced to subtyping, (after 1 single step). 
The termination for existential variable entries should be simple, given the above result:

If `WF (T |- A <: ^a <: B)`:
  1. `T |- A <: ^a <: B` fails to reduce; or 
  2. `T |- A <: ^a <: B -->* T`

We just need to apply the special result above, since we know that `A` and `B` do not contain universals.

### Termination of Matching and Type Application work

If `WF (T |- A |> B =>a w)` then either:
  1. `T |- A |> B =>a w` fails to reduce; or 
  2. Exists `T'`, such that `T |- A |> B =>a w -->* T'`   where `T'` has one less work/judgement than the original list (but it may increase other things like variables/existentials)

If `WF (T |- A * B ==>a w)` then either:
  1. `T |- A * B ==>a w` fails to reduce; or 
  2. Exists T' such that ``T |- A * B ==>a w --> T'` where `T'` has one less work/judgement than the original list **and it does not introduce new variables**.

### Termination of chekcking and inference: 

TODO as exercise :), but I think the overall idea is the same. We should have some lemmas that state that after a certain number of steps one item of work is reduced.

## Overall termination

To reason about the overall termination of worklist reduction, we have to combine the results above. 

1. I think that for work/judgements, given the results above we know that we always reduce the number of work in a worklist. 

2. For the other kind of entries, processing single units of work may increase them. Basically new variables, type variable and 
existential variables entries may be added. However, for variables and type variables termination is trivial and they do not 
introduce anything else into the worklist. For existentials, as I argued above, we are able to show that they will be processed, 
resulting in a smaller worklist **without introducing any new items in the worklist**. Thus, it seems clear that the algorithm 
will terminate. 

Thus it seems we would like to have the number of work as one of the primary measures. Since this should always decrease, 
eventually resulting in a worklist that contains only variables/existentials, and in that special case, termination should 
be trivial.

## Some ideas on concrete measures

I will discuss concrete ideas for measures in the following result:

If `WF (T |- A <: B)` then either:
  1. `T |- A <: B` fails to reduce; or 
  2. Exists `T'`, such that `T |- A <: B -->* T'`   where `T'` has one less work/judgement than the original list (but it may increase other things like variables/existentials)

First of all, once we look at individual judgements, instead of the full worklist, I think we 
can find much simpler measures that can be used to prove partial results like the above.

One concreate proposal, as discussed in the previous meeting, I think that the basic idea here is that the maximum number of entries 
that we can have for processing a piece of subtyping work is essentially bounded by the `max(depth(A),depth(B))`. 
We know what is the maximum number of work entries that a single rule can be introduced. Say that is `k`. Then 
we can use `max(depth(A),depth(B))*k` as an overaproximation to the maximum number of entries that are ever created, during 
the course of processing `A <: B`.

So a measure like this (or possibly many other measures) can be used to prove the partial termination results.
