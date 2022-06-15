# First-Order Logic with Isomorphism

## General

A Python development whose primary aim is to formalize the contents of the paper

**First-Order Logic with Isomorphism**, D. Tsementzis, (2016) <a href="https://arxiv.org/abs/1603.03092">arxiv</a>

in the form of a tool that interprets the signatures of first-order logic with isomorphism ("FOLiso-signatures") into proof assistants implementing the Univalent Foundations (UF), and where "interprets", for the time being, means "write files that these proof assistants can compile."

The other aim of this development is to use this "interpretation" in order to import actual data into UF-compatible proof-assistants (e.g. UniMath in Coq) in order to store, manipulate and transform this data as if it were one of the objects of UF, i.e. a "shape" (more precisely a "homotopy type"/"infinity-groupoid"); in other words, to create "data shapes". More details can be found in the slides under Supporting Materials.

## Current State

Currently, the development allows one to define any finite inverse category and interpret it into the UniMath implementation of UF.

## Files

fics.py -- contains the implementation of finite inverse categories

hsig.py -- contains the implementation of h-signatures

glob.py -- a script to produce the n-truncated type of globular types, as an example

sst.py -- a script to produce the n-truncated type of semi-simplicial types, as an example

Demo.ipynb -- a Jupyter Notebook containing a very simple demo of fics




