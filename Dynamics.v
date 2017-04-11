(* Copyright (c) 2017, the Dart project authors.  Please see the AUTHORS file
 * for details. All rights reserved. Use of this source code is governed by a
 * BSD-style license that can be found in the LICENSE file. *)

Require Import Utf8.
Require Import Types.
Require Import List.

Module Type DynamicsSig.
  Parameter dynamic_is_magic : Prop.
End DynamicsSig.

Module StrictDynamics <: DynamicsSig.
  Definition dynamic_is_magic := False.
  Hint Unfold dynamic_is_magic.
End StrictDynamics.

Module NormalDynamics <: DynamicsSig.
  Definition dynamic_is_magic := True.
  Hint Unfold dynamic_is_magic.
End NormalDynamics.
