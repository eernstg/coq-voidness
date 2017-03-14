(* Copyright (c) 2017, the Dart project authors.  Please see the AUTHORS file
 * for details. All rights reserved. Use of this source code is governed by a
 * BSD-style license that can be found in the LICENSE file. *)

Require Import Utf8.
Require Import List.
Require Import Types.

(* Object *)
Definition ct_Object : ClassTypes := (Object, nil) :: nil.
Definition dt_Object := dt_class ct_Object.

(* A<Object> *)
Definition ct_A_Object := (A, dt_Object :: nil) :: ct_Object.
Definition dt_A_Object := dt_class ct_A_Object.

(* A<void> *)
Definition ct_A_void := (A, dt_void :: nil) :: ct_Object.
Definition dt_A_void := dt_class ct_A_void.

(* A<dynamic> *)
Definition ct_A_dynamic := (A, dt_dynamic :: nil) :: ct_Object.
Definition dt_A_dynamic := dt_class ct_A_dynamic.

(* Iterable<Object> *)
Definition ct_Iterable_Object := (Iterable, dt_Object :: nil) :: ct_Object.
Definition dt_Iterable_Object := dt_class ct_Iterable_Object.

(* Iterable<void> *)
Definition ct_Iterable_void := (Iterable, dt_void :: nil) :: ct_Object.
Definition dt_Iterable_void := dt_class ct_Iterable_void.

(* List<Object> *)
Definition ct_List_Object := (List, dt_Object :: nil) :: ct_Iterable_Object.
Definition dt_List_Object := dt_class ct_List_Object.

(* List<void> *)
Definition ct_List_void := (List, dt_void :: nil) :: ct_Iterable_void.
Definition dt_List_void := dt_class ct_List_void.

Hint Unfold
  ct_Object dt_Object ct_A_Object dt_A_Object ct_A_void dt_A_void
  ct_A_dynamic dt_A_dynamic ct_Iterable_Object dt_Iterable_Object
  ct_Iterable_void dt_Iterable_void ct_List_Object dt_List_Object
  ct_List_void dt_List_void.
