(*----------------------------------------------------------------------------
    Copyright (c) 2016 Inhabited Type LLC.

    All rights reserved.

    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions
    are met:

    1. Redistributions of source code must retain the above copyright
       notice, this list of conditions and the following disclaimer.

    2. Redistributions in binary form must reproduce the above copyright
       notice, this list of conditions and the following disclaimer in the
       documentation and/or other materials provided with the distribution.

    3. Neither the name of the author nor the names of his contributors
       may be used to endorse or promote products derived from this software
       without specific prior written permission.

    THIS SOFTWARE IS PROVIDED BY THE CONTRIBUTORS ``AS IS'' AND ANY EXPRESS
    OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
    WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
    DISCLAIMED.  IN NO EVENT SHALL THE AUTHORS OR CONTRIBUTORS BE LIABLE FOR
    ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
    DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
    OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
    HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
    STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
    ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
    POSSIBILITY OF SUCH DAMAGE.
  ----------------------------------------------------------------------------*)

module Bigarray = struct
  (* Do not access Bigarray operations directly. If anything's needed, refer to
   * the internal Bigstring module. *)
end

type bigstring = Bigstringaf.t


module Unbuffered = struct
  include Parser

  type more = More.t =
    | Complete
    | Incomplete

  let continue = eval_continue
end

include Unbuffered
include Parser.Monad
include Parser.Choice

type 'a t = 'a u

module Buffered = struct
  type unconsumed = Buffering.unconsumed =
    { buf : bigstring
    ; off : int
    ; len : int }

  type input =
    [ `Bigstring of bigstring
    | `String    of string ]

  type 'a state =
    | Partial of ([ input | `Eof ] -> 'a state)
    | Done    of unconsumed * 'a
    | Fail    of unconsumed * string list * string

  let from_unbuffered_state ~f buffering = function
    | Unbuffered.Partial p         -> Partial (f p)
    | Unbuffered.Done(consumed, v) ->
      let unconsumed = Buffering.unconsumed ~shift:consumed buffering in
      Done(unconsumed, v)
    | Unbuffered.Fail(consumed, marks, msg) ->
      let unconsumed = Buffering.unconsumed ~shift:consumed buffering in
      Fail(unconsumed, marks, msg)

  let parse ?(initial_buffer_size=0x1000) p =
    if initial_buffer_size < 1 then
      failwith "parse: invalid argument, initial_buffer_size < 1";
    let buffering = Buffering.create initial_buffer_size in
    let rec f p input =
      Buffering.shift buffering p.committed;
      let more : More.t =
        match input with
        | `Eof            -> Complete
        | #input as input ->
          Buffering.feed_input buffering input;
          Incomplete
      in
      let for_reading = Buffering.for_reading buffering in
      eval_continue for_reading ~off:0 ~len:(Bigstringaf.length for_reading)
        more p.continue
      |> from_unbuffered_state buffering ~f
    in
    Unbuffered.parse p
    |> from_unbuffered_state buffering ~f

  let feed state input =
    match state with
    | Partial k -> k input
    | Fail(unconsumed, marks, msg) ->
      begin match input with
      | `Eof   -> state
      | #input as input ->
        let buffering = Buffering.of_unconsumed unconsumed in
        Buffering.feed_input buffering input;
        Fail(Buffering.unconsumed buffering, marks, msg)
      end
    | Done(unconsumed, v) ->
      begin match input with
      | `Eof   -> state
      | #input as input ->
        let buffering = Buffering.of_unconsumed unconsumed in
        Buffering.feed_input buffering input;
        Done(Buffering.unconsumed buffering, v)
      end

  let state_to_option = function
    | Done(_, v) -> Some v
    | _          -> None

  let state_to_result = function
    | Partial _           -> Error "incomplete input"
    | Done(_, v)          -> Ok v
    | Fail(_, marks, msg) -> Error (Unbuffered.fail_to_string marks msg)

  let state_to_unconsumed = function
    | Done(unconsumed, _)
    | Fail(unconsumed, _, _) -> Some unconsumed
    | _                      -> None

end

let parse_bigstring p bs =
  Unbuffered.parse_bigstring p bs

let parse_string p s =
  let len = String.length s in
  let bs  = Bigstringaf.create len in
  Bigstringaf.unsafe_blit_from_string s ~src_off:0 bs ~dst_off:0 ~len;
  parse_bigstring p bs


(** BEGIN: getting input *)

let unsafe_apply len ~f = Unsafe_apply(len, f)

let unsafe_apply_opt len ~f = Unsafe_apply_opt(len, f)

let ensure n p = Ensure(n, p)

(** END: getting input *)

let at_end_of_input = At_end_of_input

let end_of_input =
  at_end_of_input
  >>= function
    | true  -> return ()
    | false -> fail "end_of_input"

let advance n =
  if n < 0
  then fail "advance"
  else ensure n (Advance n)

let pos = Pos

let available = Available

let commit = Commit

let peek_char = Peek_char

(* This parser is too important to not be optimized. Do a custom job. *)
let peek_char_fail = Peek_char_fail

let satisfy f = Satisfy f

let char c = ensure 1 (Char c)

let not_char c = ensure 1 (Not_char c)

let any_char = ensure 1 Any_char

let int8 i = ensure 1 (Int8 i)

let any_uint8 = ensure 1 Any_uint8

let any_int8 = ensure 1 Any_int8

let skip f = ensure 1 (Skip f)

let count_while ~init ~f ~with_buffer =
  Count_while(init, f, with_buffer)

let count_while1 ~f ~with_buffer = Count_while1(f, with_buffer)

let string_ f s =
  (* XXX(seliopou): Inefficient. Could check prefix equality to short-circuit
   * the io. *)
  let len = String.length s in
  ensure  len (unsafe_apply_opt len ~f:(fun buffer ~off ~len ->
    let i = ref 0 in
    while !i < len && Char.equal (f (Bigstringaf.unsafe_get buffer (off + !i)))
                                 (f (String.unsafe_get s !i))
    do
      incr i
    done;
    if len = !i
    then Ok (Bigstringaf.substring buffer ~off ~len)
    else Error "string"))

let string s    = string_ (fun x -> x) s
let string_ci s = string_ Char.lowercase_ascii s

let skip_while f =
  count_while ~init:0 ~f ~with_buffer:(fun _ ~off:_ ~len:_ -> ())

let take n =
  let n = max n 0 in
  ensure n (unsafe_apply n ~f:Bigstringaf.substring)

let take_bigstring n =
  let n = max n 0 in
  ensure n (unsafe_apply n ~f:Bigstringaf.copy)

let take_bigstring_while f =
  count_while ~init:0 ~f ~with_buffer:Bigstringaf.copy

let take_bigstring_while1 f =
  count_while1 ~f ~with_buffer:Bigstringaf.copy

let take_bigstring_till f =
  take_bigstring_while (fun c -> not (f c))

let peek_string n =
  Unsafe_lookahead (take n)

let take_while f =
  count_while ~init:0 ~f ~with_buffer:Bigstringaf.substring

let take_while1 f =
  count_while1 ~f ~with_buffer:Bigstringaf.substring

let take_till f =
  take_while (fun c -> not (f c))

let choice ?(failure_msg="no more choices") ps =
  List.fold_right (<|>) ps (fail failure_msg)

let option x p =
  p <|> return x

let cons x xs = x :: xs

let rec list ps =
  match ps with
  | []    -> return []
  | p::ps -> lift2 cons p (list ps)

let count n p =
  if n < 0 then
    failwith "count: invalid argument, n < 0";
  let rec loop = function
    | 0 -> return []
    | n -> lift2 cons p (loop (n - 1))
  in
  loop n

let many p =
  fix (fun m ->
    (lift2 cons p m) <|> return [])

let many1 p =
  lift2 cons p (many p)

let many_till p t =
  fix (fun m ->
    (t *> return []) <|> (lift2 cons p m))

let sep_by1 s p =
  fix (fun m ->
    lift2 cons p ((s *> m) <|> return []))

let sep_by s p =
  (lift2 cons p ((s *> sep_by1 s p) <|> return [])) <|> return []

let skip_many p =
  fix (fun m ->
    (p *> m) <|> return ())

let skip_many1 p =
  p *> skip_many p

let end_of_line =
  (char '\n' *> return ()) <|> (string "\r\n" *> return ()) <?> "end_of_line"

let scan_ state f ~with_buffer = Scan(state, f, with_buffer)

let scan state f =
  scan_ state f ~with_buffer:Bigstringaf.substring

let scan_state state f =
  scan_ state f ~with_buffer:(fun _ ~off:_ ~len:_ -> ())
  >>| fun ((), state) -> state

let scan_string state f =
  scan state f >>| fst

module BE = struct
  (* XXX(seliopou): The pattern in both this module and [LE] are a compromise
   * between efficiency and code reuse. By inlining [ensure] you can recover
   * about 2 nanoseconds on average. That may add up in certain applications.
   *
   * This pattern does not allocate in the fast (success) path.
   * *)
  let int16 n =
    let bytes = 2 in
    ensure bytes (BE_int16 n)

  let int32 n =
    let bytes = 4 in
    ensure bytes (BE_int32 n)

  let int64 n =
    let bytes = 8 in
    ensure bytes (BE_int64 n)

  let any_uint16 =
    ensure 2 (unsafe_apply 2 ~f:(fun bs ~off ~len:_ -> Bigstringaf.unsafe_get_int16_be bs off))

  let any_int16  =
    ensure 2 (unsafe_apply 2 ~f:(fun bs ~off ~len:_ -> Bigstringaf.unsafe_get_int16_sign_extended_be  bs off))

  let any_int32  =
    ensure 4 (unsafe_apply 4 ~f:(fun bs ~off ~len:_ -> Bigstringaf.unsafe_get_int32_be bs off))

  let any_int64 =
    ensure 8 (unsafe_apply 8 ~f:(fun bs ~off ~len:_ -> Bigstringaf.unsafe_get_int64_be bs off))

  let any_float =
    ensure 4 (unsafe_apply 4 ~f:(fun bs ~off ~len:_ -> Int32.float_of_bits (Bigstringaf.unsafe_get_int32_be bs off)))

  let any_double =
    ensure 8 (unsafe_apply 8 ~f:(fun bs ~off ~len:_ -> Int64.float_of_bits (Bigstringaf.unsafe_get_int64_be bs off)))
end

module LE = struct
  let int16 n =
    let bytes = 2 in
    ensure bytes (LE_int16 n)

  let int32 n =
    let bytes = 4 in
    ensure bytes (LE_int32 n)

  let int64 n =
    let bytes = 8 in
    ensure bytes (LE_int64 n)


  let any_uint16 =
    ensure 2 (unsafe_apply 2 ~f:(fun bs ~off ~len:_ -> Bigstringaf.unsafe_get_int16_le bs off))

  let any_int16  =
    ensure 2 (unsafe_apply 2 ~f:(fun bs ~off ~len:_ -> Bigstringaf.unsafe_get_int16_sign_extended_le  bs off))

  let any_int32  =
    ensure 4 (unsafe_apply 4 ~f:(fun bs ~off ~len:_ -> Bigstringaf.unsafe_get_int32_le bs off))

  let any_int64 =
    ensure 8 (unsafe_apply 8 ~f:(fun bs ~off ~len:_ -> Bigstringaf.unsafe_get_int64_le bs off))

  let any_float =
    ensure 4 (unsafe_apply 4 ~f:(fun bs ~off ~len:_ -> Int32.float_of_bits (Bigstringaf.unsafe_get_int32_le bs off)))

  let any_double =
    ensure 8 (unsafe_apply 8 ~f:(fun bs ~off ~len:_ -> Int64.float_of_bits (Bigstringaf.unsafe_get_int64_le bs off)))
end

module Unsafe = struct
  let take n f =
    let n = max n 0 in
    ensure n (unsafe_apply n ~f)

  let peek n f =
    Unsafe_lookahead (take n f)

  let take_while check f =
    count_while ~init:0 ~f:check ~with_buffer:f

  let take_while1 check f =
    count_while1 ~f:check ~with_buffer:f

  let take_till check f =
    take_while (fun c -> not (check c)) f
end
