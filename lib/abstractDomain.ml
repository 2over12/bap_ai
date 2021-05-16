
(***********************************************************************)
(*                                                                     *)
(* Copyright (c) 2007-present.                                         *)
(* Programming Research Laboratory (ROPAS), Seoul National University. *)
(* All rights reserved.                                                *)
(*                                                                     *)
(* This software is distributed under the term of the BSD license.     *)
(* See the LICENSE file for details.                                   *)
(*                                                                     *)
(***********************************************************************)
(** Signature for abstract domain *)

(** Signature of set *)
open Core_kernel
module type SET =
sig
  include Comparable
  val t_of_sexp : Sexplib0.Sexp.t -> t

  val sexp_of_t : t -> Sexplib0.Sexp.t
end

module type HASHABLE_SET =
sig
  include SET
  val equal     : t -> t -> bool
  val hash      : t -> int
end

(** Signature of CPO *)
module type CPO =
sig
  include SET

  val le : t -> t -> bool
  val eq : t -> t -> bool

  val bot : t

  val join : t -> t -> t
  val meet : t -> t -> t

  val widen : t -> t -> t
  val narrow : t -> t -> t
end

(** Signature of lattice *)
module type LAT =
sig
  include CPO
  val top : t
end