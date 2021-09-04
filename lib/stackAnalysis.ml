(*
Simple stack analysis to get initial A-locs

We need to get for each access to esp/ebp the current stack depth

Dump simple stack size dataflow: https://www2.cs.arizona.edu/~debray/Publications/stack-analysis.pdf


http://seclab.cs.sunysb.edu/seclab/pubs/ruith.pdf ASA type stuff

ASA versus VSA: https://ir.stonybrook.edu/xmlui/bitstream/handle/11401/71535/Saberi_grad.sunysb_0771M_11246.pdf?sequence=5

ASA paper: http://www.seclab.cs.sunysb.edu/seclab/pubs/cgo065-saxena.pdf



DIVINE: https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.67.1019&rep=rep1&type=pdf


Secondwrite papers:
unsound pointer analysis for var recovery: http://web.cse.ohio-state.edu/~rountev.1/5343/pdf/pldi13.pdf
Full system: https://terpconnect.umd.edu/~barua/anand-EUROSYS-2013.pdf


Numeric domain Relational Bitvectors: https://research.cs.wisc.edu/wpis/papers/tr1789.pdf


K-domains for control flow recovery:
https://d-nb.info/1008875570/34 bounded address tracking, thesis
https://www.cs.utexas.edu/users/hunt/FMCAD/FMCAD10/Papers/papers/04Session3/009Kinder.pdf original paper


more precise heap abstraction: https://research.cs.wisc.edu/wpis/papers/sas06-recency.pdf


Papers that use Init reg abstraction for UAF:
https://tel.archives-ouvertes.fr/tel-01681707v2/document thesis



So the idea here is to try to make init regs sound but converge by bounding the number of accesses we will split

*)

open Bap.Std
open Graphlib.Std
open Core_kernel


