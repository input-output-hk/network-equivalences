Overview
========

The `network-equivalences` library contains proofs of behavioral
equivalences of various communication networks. For reasoning on an
appropriately high level, it introduces and uses a communication
language that is embedded in [the Þ-calculus][thorn-calculus].

Part of this library are discussed in the following conference articles:
  * [Correctness of Broadcast via Multicast: Graphically and
    Formally](https://arxiv.org/abs/2209.09472)
  * [Proofs about Network Communication: For Humans and
    Machines](https://arxiv.org/abs/2308.10652)

[thorn-calculus]:
    https://github.com/input-output-hk/thorn-calculus
    "Þ-calculus"


Requirements
============

You need Isabelle2022 to use this Isabelle library. You can obtain
Isabelle2022 from the [Isabelle website][isabelle].

[isabelle]:
    https://isabelle.in.tum.de/
    "Isabelle"

In addition, you need the following Isabelle sessions:

  * [`Thorn_Calculus`](https://github.com/input-output-hk/thorn-calculus)


Setup
=====

To make this Isabelle library available to your Isabelle installation,
add the path of the `src` directory to the file
`$ISABELLE_HOME_USER/ROOTS`. You can find out the value of
`$ISABELLE_HOME_USER` by running the following command:

    isabelle getenv ISABELLE_HOME_USER


Building
========

Running `make` builds the PDF file that includes the documentation and
the code and places it in `$ISABELLE_BROWSER_INFO/IOG`. You can find out
the value of `$ISABELLE_BROWSER_INFO` by running the following command:

    isabelle getenv ISABELLE_BROWSER_INFO

The makefile specifies two targets: `properly`, which is the default,
and `qnd`. With `properly`, fake proofs (`sorry`) are not accepted; with
`qnd`, quick-and-dirty mode is used and thus fake proofs are accepted.
