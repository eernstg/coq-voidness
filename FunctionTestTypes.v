(* Copyright (c) 2017, the Dart project authors.  Please see the AUTHORS file
 * for details. All rights reserved. Use of this source code is governed by a
 * BSD-style license that can be found in the LICENSE file. *)

Require Import Utf8.
Require Import Types.

(* Object *)
Definition ct_Object : NameDartTypes := ndts_cons (Object, dts_nil) ndts_nil.
Definition dt_Object := dt_class ct_Object.

(* Function types *)
Definition dt_fun_void_void :=
  dt_function dt_void (dts_cons dt_void dts_nil).
Definition dt_fun_void_dynamic :=
  dt_function dt_dynamic (dts_cons dt_void dts_nil).
Definition dt_fun_void_Object :=
  dt_function dt_Object (dts_cons dt_void dts_nil).
Definition dt_fun_dynamic_void :=
  dt_function dt_void (dts_cons dt_dynamic dts_nil).
Definition dt_fun_dynamic_dynamic :=
  dt_function dt_dynamic (dts_cons dt_dynamic dts_nil).
Definition dt_fun_dynamic_Object :=
  dt_function dt_Object (dts_cons dt_dynamic dts_nil).
Definition dt_fun_Object_Object :=
  dt_function dt_Object (dts_cons dt_Object dts_nil).
Definition dt_fun_Object_void :=
  dt_function dt_void (dts_cons dt_Object dts_nil).
Definition dt_fun_Object_dynamic :=
  dt_function dt_dynamic (dts_cons dt_Object dts_nil).
Definition dt_fun2_void_void :=
  dt_function dt_dynamic (dts_cons dt_fun_void_void dts_nil).
Definition dt_fun2_void_dynamic :=
  dt_function dt_dynamic (dts_cons dt_fun_void_dynamic dts_nil).
Definition dt_fun2_void_Object :=
  dt_function dt_dynamic (dts_cons dt_fun_void_Object dts_nil).
Definition dt_fun2_dynamic_void :=
  dt_function dt_dynamic (dts_cons dt_fun_dynamic_void dts_nil).
Definition dt_fun2_dynamic_dynamic :=
  dt_function dt_dynamic (dts_cons dt_fun_dynamic_dynamic dts_nil).
Definition dt_fun2_dynamic_Object :=
  dt_function dt_dynamic (dts_cons dt_fun_dynamic_Object dts_nil).
Definition dt_fun2_Object_void :=
  dt_function dt_dynamic (dts_cons dt_fun_Object_void dts_nil).
Definition dt_fun2_Object_dynamic :=
  dt_function dt_dynamic (dts_cons dt_fun_Object_dynamic dts_nil).
Definition dt_fun2_Object_Object :=
  dt_function dt_dynamic (dts_cons dt_fun_Object_Object dts_nil).

Hint Unfold
  ct_Object dt_Object
  dt_fun_void_void dt_fun_void_dynamic dt_fun_void_Object
  dt_fun_dynamic_void dt_fun_dynamic_dynamic dt_fun_dynamic_Object
  dt_fun_Object_Object dt_fun_Object_void dt_fun_Object_dynamic
  dt_fun2_void_void dt_fun2_void_dynamic dt_fun2_void_Object
  dt_fun2_dynamic_void dt_fun2_dynamic_dynamic dt_fun2_dynamic_Object
  dt_fun2_Object_void dt_fun2_Object_dynamic dt_fun2_Object_Object.
