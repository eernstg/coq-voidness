(* Copyright (c) 2017, the Dart project authors.  Please see the AUTHORS file
 * for details. All rights reserved. Use of this source code is governed by a
 * BSD-style license that can be found in the LICENSE file. *)

Require Import Utf8.
Require Import Coq.Program.Basics.
Require Import Types.
Require Import Subtypes.
Require Import ClassTestTypes.

(* Model `A<Null>`, `A<A<Null>>`, `A<A<A<Null>>>`, ... *)
Fixpoint nestedType (n : nat) : DartType :=
  match n with
    | O => dt_bottom
    | S n => dt_class (ndts_cons (A, dts_cons (nestedType n) dts_nil) ct_Object)
  end.

Lemma DartTypeHasInfiniteChain : ∀ n,
  DartSubtype (nestedType n) (nestedType (S n)).
Proof.
  induction n; simpl; auto.
  apply ds_class. apply dsscts_cons.
  - apply dscts_first. apply dsct_args. apply dsp_cons; auto.
  - apply dsscts_cons; auto. apply dscts_rest. apply dscts_first.
    apply dsct_args; auto.
Qed.
