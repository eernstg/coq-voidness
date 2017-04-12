(* Copyright (c) 2017, the Dart project authors.  Please see the AUTHORS file
 * for details. All rights reserved. Use of this source code is governed by a
 * BSD-style license that can be found in the LICENSE file. *)

Require Import Utf8.
Require Import Coq.Program.Basics.

Inductive Name : Set := Object | A | B | N | C1 | T | Iterable | List.

Unset Elimination Schemes.

Inductive DartType : Set :=
| dt_void : DartType
| dt_dynamic : DartType
| dt_class : NameDartTypes -> DartType (* Incl. all clausal supertypes *)
| dt_function : DartType -> DartTypes -> DartType
| dt_variable : Name -> DartType (* Type parameter with no bound: can be void *)
| dt_bottom : DartType

with DartTypes : Set :=
| dts_nil : DartTypes
| dts_cons : DartType -> DartTypes -> DartTypes

with NameDartTypes : Set :=
| ndts_nil : NameDartTypes
| ndts_cons : Name -> DartTypes -> NameDartTypes -> NameDartTypes.

Scheme DartType_ind := Induction for DartType Sort Prop
  with DartTypes_ind := Induction for DartTypes Sort Prop
  with NameDartTypes_ind := Induction for NameDartTypes Sort Prop.

Combined Scheme DartType_mutind from
  DartType_ind, DartTypes_ind, NameDartTypes_ind.

Set Elimination Schemes.
