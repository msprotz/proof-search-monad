(*****************************************************************************)
(*  Mezzo, a programming language based on permissions                       *)
(*  Copyright (C) 2011, 2012 Jonathan Protzenko and François Pottier         *)
(*                                                                           *)
(*  This program is free software: you can redistribute it and/or modify     *)
(*  it under the terms of the GNU General Public License as published by     *)
(*  the Free Software Foundation, either version 3 of the License, or        *)
(*  (at your option) any later version.                                      *)
(*                                                                           *)
(*  This program is distributed in the hope that it will be useful,          *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(*  GNU General Public License for more details.                             *)
(*                                                                           *)
(*  You should have received a copy of the GNU General Public License        *)
(*  along with this program.  If not, see <http://www.gnu.org/licenses/>.    *)
(*                                                                           *)
(*****************************************************************************)

(** This module implements lazy lists. *)

type 'a t = 'a node Lazy.t
and 'a node = Nil | Cons of 'a * 'a t

val of_list: 'a list -> 'a t
val nil : 'a t
val cons : 'a -> 'a t -> 'a t
val next : 'a t -> 'a node
val tl : 'a t -> 'a t
val hd : 'a t -> 'a
val one : 'a -> 'a t
val filter : ('a -> bool) -> 'a t -> 'a t
val flatten : 'a t list -> 'a t
val flattenl : 'a t t -> 'a t
val map : ('a -> 'b) -> 'a t -> 'b t
val concat : 'a t t -> 'a t
val iter : ('a -> unit) -> 'a t -> unit
val find : ('a -> bool) -> 'a t -> 'a
val exists : ('a -> bool) -> 'a t -> bool
