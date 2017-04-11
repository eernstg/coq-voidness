(* Copyright (c) 2017, the Dart project authors.  Please see the AUTHORS file
 * for details. All rights reserved. Use of this source code is governed by a
 * BSD-style license that can be found in the LICENSE file. *)

Require Import Utf8.
Require Import Coq.Program.Basics.
Require Import List.

Inductive Name : Set := Object | A | B | N | C1 | T | Iterable | List.

Inductive DartType : Set :=
| dt_void : DartType
| dt_dynamic : DartType
| dt_class : list (Name * list DartType) -> DartType (* Incl. all clausal supertypes *)
| dt_function : DartType -> list DartType -> DartType
| dt_variable : Name -> DartType (* Type parameter with no bound: can be void *)
| dt_bottom : DartType.

Definition ClassType : Type := (Name * (list DartType))%type.
Definition ClassTypes : Type := list ClassType.
