type 'a with_state = Input.t ->  int -> More.t -> 'a

type 'a state =
  | Partial of 'a partial
  | Done    of int * 'a
  | Fail    of int * string list * string

and 'a partial =
  { committed : int; continue: 'a continue }

and 'a continue =
  Continue :
    { parser_uncommitted_bytes : int
    ; parser_committed_bytes : int
    ; pos : int
    ; resume : 'b u
    ; complete : 'b u
    ; succ : ('b, 'a) success
    ; fail : 'a failure } -> 'a continue

and 'a u =
  | Return : 'a -> 'a u
  | Failure : string -> 'a u
  | Bind : 'a u * ('a -> 'b u) -> 'b u
  | Map : 'a u * ('a -> 'b) -> 'b u
  | Map2 : 'a u * 'b u * ('a -> 'b -> 'c) -> 'c u
  | Map3 : 'a u * 'b u * 'c u * ('a -> 'b -> 'c -> 'd) -> 'd u
  | Map4 : 'a u * 'b u * 'c u * 'd u * ('a -> 'b -> 'c -> 'd -> 'e) -> 'e u
  | App : ('a -> 'b) u * 'a u -> 'b u
  | Seq_right : 'a u * 'b u -> 'b u
  | Seq_left : 'a u * 'b u -> 'a u
  | Mark : 'a u * string -> 'a u
  | Choice : 'a u * 'a u -> 'a u
  | Lazy : 'a u Lazy.t -> 'a u
  | Ensure_suspended : int -> unit u
  | Unsafe_apply : int * (Bigstringaf.t -> off:int -> len:int -> 'a) -> 'a u
  | Unsafe_apply_opt
    : int * (Bigstringaf.t -> off:int -> len:int -> ('a, string) result) -> 'a u
  | Ensure : int * 'a u -> 'a u
  | At_end_of_input : bool u
  | Advance : int -> unit u
  | Pos : int u
  | Available : int u
  | Commit : unit u
  | Unsafe_lookahead : 'a u -> 'a u
  | Peek_char_suspended : char option u
  | Peek_char : char option u
  | Peek_char_fail : char u
  | Satisfy : (char -> bool) -> char u
  | Char : char -> char u
  | Not_char : char -> char u
  | Any_char : char u
  | Int8 : int -> int u
  | Any_uint8 : int u
  | Any_int8 : int u
  | Skip : (char -> bool) -> unit u
  | Count_while :
      int * (char -> bool) * (Bigstringaf.t -> off:int -> len:int -> 'a) -> 'a u
  | Count_while1 :
      (char -> bool) * (Bigstringaf.t -> off:int -> len:int -> 'a) -> 'a u
  | Scan :
      'b * ('b -> char -> 'b option) * (Bigstringaf.t -> off:int -> len:int -> 'a)
    -> ('a * 'b) u
  | BE_int16 : int -> unit u
  | BE_int32 : Int32.t -> unit u
  | BE_int64 : Int64.t -> unit u
  | LE_int16 : int -> unit u
  | LE_int32 : Int32.t -> unit u
  | LE_int64 : Int64.t -> unit u

and ('a, 'r) success =
  | Succ_done : ('a, 'a) success
  | Succ_bind : ('a -> 'b u) * 'r failure * ('b, 'r) success -> ('a, 'r) success
  | Succ_map : ('a -> 'b) * ('b, 'r) success -> ('a, 'r) success
  | Succ_app : 'a u * 'r failure * ('b, 'r) success -> ('a -> 'b, 'r) success
  | Succ_map21 : ('a -> 'b -> 'c) * 'b u * 'r failure * ('c, 'r) success -> ('a, 'r) success
  | Succ_map22 : ('a -> 'b -> 'c) * 'a * ('c, 'r) success -> ('b, 'r) success
  | Succ_map31 :
      ('a -> 'b -> 'c -> 'd) * 'b u * 'c u * 'r failure * ('d, 'r) success-> ('a, 'r) success
  | Succ_map32 :
      ('a -> 'b -> 'c -> 'd) * 'a * 'c u * 'r failure * ('d, 'r) success -> ('b, 'r) success
  | Succ_map33 :
      ('a -> 'b -> 'c -> 'd) * 'a * 'b * ('d, 'r) success -> ('c, 'r) success
  | Succ_map41 :
      ('a -> 'b -> 'c -> 'd -> 'e) * 'b u * 'c u * 'd u
      * 'r failure * ('e, 'r) success-> ('a, 'r) success
  | Succ_map42 :
      ('a -> 'b -> 'c -> 'd -> 'e) * 'a * 'c u * 'd u
      * 'r failure * ('e, 'r) success -> ('b, 'r) success
  | Succ_map43 :
      ('a -> 'b -> 'c -> 'd -> 'e) * 'a * 'b * 'd u
      * 'r failure * ('e, 'r) success-> ('c, 'r) success
  | Succ_map44 :
      ('a -> 'b -> 'c -> 'd -> 'e) * 'a * 'b * 'c * ('e, 'r) success-> ('d, 'r) success
  | Succ_seq_right : 'b u * 'r failure * ('b, 'r) success -> ('a, 'r) success
  | Succ_seq_left : 'b u * 'r failure * ('a, 'r) success -> ('a, 'r) success
  | Succ_const : 'a * ('a, 'r) success -> ('b, 'r) success
  | Succ_reposition : int * ('a, 'r) success -> ('a, 'r) success
  | Succ_satisfy :
      (char -> bool) * 'r failure * (char, 'r) success -> ('a, 'r) success

and 'r failure =
  | Fail_fail : 'r failure
  | Fail_mark : string * 'r failure -> 'r failure
  | Fail_choice : int * More.t * 'a u * 'r failure * ('a, 'r) success -> 'r failure


let prompt input pos resume complete fail succ =
  (* [prompt] should only call [succ] if it has received more input. If there
   * is no chance that the input will grow, i.e., [more = Complete], then
   * [prompt] should call [fail]. Otherwise (in the case where the input
   * hasn't grown but [more = Incomplete] just prompt again. *)
  let parser_uncommitted_bytes = Input.parser_uncommitted_bytes input in
  let parser_committed_bytes   = Input.parser_committed_bytes input in
  let committed = Input.bytes_for_client_to_commit input in
  let continue =
    Continue { parser_uncommitted_bytes; parser_committed_bytes;
        pos; resume; complete; succ; fail }
  in
  Partial { committed; continue }

let fail_to_string marks err =
  String.concat " > " marks ^ ": " ^ err

let state_to_option = function
  | Done(_, v) -> Some v
  | _          -> None

let state_to_result = function
  | Done(_, v)          -> Ok v
  | Partial _           -> Error "incomplete input"
  | Fail(_, marks, err) -> Error (fail_to_string marks err)

let return_true = Return true
let return_false = Return false
let return_none = Return None
let not_enough_input_msg = "not enough input"
let not_enough_input = Failure not_enough_input_msg
let fail_count_while1_msg = "count_while1"
let fail_count_while1 = Failure fail_count_while1_msg

(* https://graphics.stanford.edu/~seander/bithacks.html#VariableSignExtendRisky *)
let int8_shift = Sys.int_size - 8

let rec eval :
  type a r. (r failure -> (a, r) success -> a u -> r state) with_state =
  fun input pos more fail succ -> function
    | Return v -> eval_success input pos more v succ
    | Failure msg -> eval_failure input pos more [] msg fail
    | Bind(p, f) ->
      let succ' = Succ_bind(f, fail, succ) in
      eval input pos more fail succ' p
    | Map(p, f) ->
      let succ' = Succ_map(f, succ) in
      eval input pos more fail succ' p
    | App(f, m) ->
      let succ' = Succ_app(m, fail, succ) in
      eval input pos more fail succ' f
    | Map2(pa, pb, f) ->
      let succ' = Succ_map21(f, pb, fail, succ) in
      eval input pos more fail succ' pa
    | Map3(pa, pb, pc, f) ->
      let succ' = Succ_map31(f, pb, pc, fail, succ) in
      eval input pos more fail succ' pa
    | Map4(pa, pb, pc, pd, f) ->
      let succ' = Succ_map41(f, pb, pc, pd, fail, succ) in
      eval input pos more fail succ' pa
    | Seq_right(pa, pb) ->
      let succ' = Succ_seq_right(pb, fail, succ) in
      eval input pos more fail succ' pa
    | Seq_left(pa, pb) ->
      let succ' = Succ_seq_left(pb, fail, succ) in
      eval input pos more fail succ' pa
    | Mark(p, mark) ->
      let fail' = Fail_mark(mark, fail) in
      eval input pos more fail' succ p
    | Choice(p1, p2) ->
      let fail' = Fail_choice(pos, more, p2, fail, succ) in
      eval input pos more fail' succ p1
    | Lazy (lazy p) ->
      eval input pos more fail succ p
    | Ensure_suspended n ->
      if pos + n <= Input.length input then
        eval_success input pos more () succ
      else begin
        match (more : More.t) with
        | Complete   -> eval_failure input pos more [] not_enough_input_msg fail
        | Incomplete ->
          prompt input pos (Ensure_suspended n) not_enough_input fail succ
      end
    | Ensure(n, p) ->
      if pos + n <= Input.length input
      then eval input pos more fail succ p
      else begin
        match (more : More.t) with
        | Complete   -> eval_failure input pos more [] not_enough_input_msg fail
        | Incomplete ->
          let succ' = Succ_seq_right(p, fail, succ) in
          prompt input pos (Ensure_suspended n) not_enough_input fail succ'
      end
    | Unsafe_apply(len, f) ->
        eval_success input (pos + len) more (Input.apply input pos len ~f) succ
    | Unsafe_apply_opt(len, f) -> begin
        match Input.apply input pos len ~f with
        | Error e -> eval_failure input pos more [] e fail
        | Ok    x -> eval_success input (pos + len) more x succ
      end
    | At_end_of_input -> begin
        if pos < Input.length input then
          eval_success input pos more false succ
        else match more with
          | Complete -> eval_success input pos more true succ
          | Incomplete -> prompt input pos return_false return_true fail succ
      end
    | Advance n -> eval_success input (pos + n) more () succ
    | Pos -> eval_success input pos more pos succ
    | Available -> eval_success input pos more (Input.length input - pos) succ
    | Commit ->
      Input.commit input pos;
      eval_success input pos more () succ
    | Unsafe_lookahead p ->
      let succ' = Succ_reposition(pos, succ) in
      eval input pos more fail succ' p
    | Peek_char_suspended ->
      eval_success input pos more (Some (Input.unsafe_get_char input pos)) succ
    | Peek_char -> begin
        if pos < Input.length input then
          eval_success input pos more (Some (Input.unsafe_get_char input pos)) succ
        else if more = Complete then
          eval_success input pos more None succ
        else
          prompt input pos return_none Peek_char_suspended fail succ
      end
    | Peek_char_fail -> begin
        if pos < Input.length input
        then eval_success input pos more (Input.unsafe_get_char input pos) succ
        else
          let succ' = Succ_seq_right(Peek_char_fail, fail, succ) in
          match (more : More.t) with
          | Complete   -> eval_failure input pos more [] not_enough_input_msg fail
          | Incomplete ->
            prompt input pos (Ensure_suspended 1) not_enough_input fail succ'
      end
    | Satisfy f -> begin
        if pos < Input.length input then
          let c = Input.unsafe_get_char input pos in
          if f c
          then eval_success input (pos + 1) more c succ
          else eval_failure input pos more [] "satisfy" fail
        else
          let succ' = Succ_satisfy(f, fail, succ) in
          match (more : More.t) with
          | Complete   -> eval_failure input pos more [] not_enough_input_msg fail
          | Incomplete ->
            prompt input pos (Ensure_suspended 1) not_enough_input fail succ'
      end
    | Char c -> begin
        if Input.unsafe_get_char input pos = c
        then eval_success input (pos + 1) more c succ
        else eval_failure input pos more [] (Printf.sprintf "char %C" c) fail
      end
    | Not_char c -> begin
        let c' = Input.unsafe_get_char input pos in
        if c <> c'
        then eval_success input (pos + 1) more c' succ
        else eval_failure input pos more [] (Printf.sprintf "not char %C" c) fail
      end
    | Any_char ->
      eval_success input (pos + 1) more (Input.unsafe_get_char input pos) succ
    | Int8 i -> begin
        let c = Char.code (Input.unsafe_get_char input pos) in
        if c = i land 0xff
        then eval_success input (pos + 1) more c succ
        else eval_failure input pos more [] (Printf.sprintf "int8 %d" i) fail
      end
    | Any_uint8 ->
      let c = Input.unsafe_get_char input pos in
      eval_success input (pos + 1) more (Char.code c) succ
    | Any_int8 ->
      let c = Input.unsafe_get_char input pos in
      eval_success input (pos + 1) more ((Char.code c lsl int8_shift) asr int8_shift) succ
    | Skip f -> begin
        if f (Input.unsafe_get_char input pos)
        then eval_success input (pos + 1) more () succ
        else eval_failure input pos more [] "skip" fail
      end
    | Count_while(init, f, with_buffer) -> begin
        let len         = Input.count_while input (pos + init) ~f in
        let input_len   = Input.length input in
        let init'       = init + len in
        (* Check if the loop terminated because it reached the end of the input
         * buffer. If so, then prompt for additional input and continue. *)
        if pos + init' < input_len || more = Complete
        then eval_success input (pos + init') more
               (Input.apply input pos init' ~f:with_buffer) succ
        else
          let resume = Count_while(init', f, with_buffer) in
          let complete = Unsafe_apply(init', with_buffer) in
          prompt input pos resume complete fail succ
        end
    | Count_while1(f, with_buffer) as orig -> begin
        let len         = Input.count_while input pos ~f in
        let input_len   = Input.length input in
        (* Check if the loop terminated because it reached the end of the input
         * buffer. If so, then prompt for additional input and continue. *)
        if len < 1
        then
          if pos < input_len || more = Complete
          then eval_failure input pos more [] fail_count_while1_msg fail
          else
            prompt input pos orig fail_count_while1 fail succ
        else if pos + len < input_len || more = Complete
        then eval_success input (pos + len) more (Input.apply input pos len ~f:with_buffer) succ
        else
          let resume = Count_while(len, f, with_buffer) in
          let complete = Unsafe_apply(len, with_buffer) in
          prompt input pos resume complete fail succ
      end
    | Scan(state, f, with_buffer) ->
        let state = ref state in
        let f c =
          match f !state c with
          | None -> false
          | Some state' -> state := state'; true
        in
        let pair x = x, !state in
        let parser = Map(Count_while(0, f, with_buffer), pair) in
        eval input pos more fail succ parser
    | BE_int16 n ->
        let bytes = 2 in
        if Input.unsafe_get_int16_be input pos = (n land 0xffff)
        then eval_success input (pos + bytes) more () succ
        else eval_failure input pos more [] "BE.int16" fail
    | BE_int32 n ->
        let bytes = 4 in
        if Int32.equal (Input.unsafe_get_int32_be input pos) n
        then eval_success input (pos + bytes) more () succ
        else eval_failure input pos more [] "BE.int32" fail
    | BE_int64 n ->
        let bytes = 8 in
        if Int64.equal (Input.unsafe_get_int64_be input pos) n
        then eval_success input (pos + bytes) more () succ
        else eval_failure input pos more [] "BE.int64" fail
    | LE_int16 n ->
        let bytes = 2 in
        if Input.unsafe_get_int16_le input pos = (n land 0xffff)
        then eval_success input (pos + bytes) more () succ
        else eval_failure input pos more [] "LE.int16" fail
    | LE_int32 n ->
        let bytes = 4 in
        if Int32.equal (Input.unsafe_get_int32_le input pos) n
        then eval_success input (pos + bytes) more () succ
        else eval_failure input pos more [] "LE.int32" fail
    | LE_int64 n ->
        let bytes = 8 in
        if Int64.equal (Input.unsafe_get_int64_le input pos) n
        then eval_success input (pos + bytes) more () succ
        else eval_failure input pos more [] "LE.int64" fail

and eval_success : type a r. (a -> (a, r) success -> r state) with_state =
  fun input pos more v -> function
  | Succ_done ->
    Done(pos - Input.client_committed_bytes input, v)
  | Succ_map(f, succ) ->
    eval_success input pos more (f v) succ
  | Succ_map21(f, pb, fail, succ) ->
    let succ' = Succ_map22(f, v, succ) in
    eval input pos more fail succ' pb
  | Succ_map22(f, a, succ) ->
    eval_success input pos more (f a v) succ
  | Succ_map31(f, pb, pc, fail, succ) ->
    let succ' = Succ_map32(f, v, pc, fail, succ) in
    eval input pos more fail succ' pb
  | Succ_map32(f, a, pc, fail, succ) ->
    let succ' = Succ_map33(f, a, v, succ) in
    eval input pos more fail succ' pc
  | Succ_map33(f, a, b, succ) ->
    eval_success input pos more (f a b v) succ
  | Succ_map41(f, pb, pc, pd, fail, succ) ->
    let succ' = Succ_map42(f, v, pc, pd, fail, succ) in
    eval input pos more fail succ' pb
  | Succ_map42(f, a, pc, pd, fail, succ) ->
    let succ' = Succ_map43(f, a, v, pd, fail, succ) in
    eval input pos more fail succ' pc
  | Succ_map43(f, a, b, pd, fail, succ) ->
    let succ' = Succ_map44(f, a, b, v, succ) in
    eval input pos more fail succ' pd
  | Succ_map44(f, a, b, c, succ) ->
    eval_success input pos more (f a b c v) succ
  | Succ_seq_right(p, fail, succ) ->
    eval input pos more fail succ p
  | Succ_seq_left(p, fail, succ) ->
    let succ' = Succ_const(v, succ) in
    eval input pos more fail succ' p
  | Succ_app(m, fail, succ)  ->
    let succ' = Succ_map(v, succ) in
    eval input pos more fail succ' m
  | Succ_bind(f, fail, succ) ->
    eval input pos more fail succ (f v)
  | Succ_const(x, succ) ->
    eval_success input pos more x succ
  | Succ_reposition(pos', succ) ->
    eval_success input pos' more v succ
  | Succ_satisfy(f, fail, succ) ->
    let c = Input.unsafe_get_char input pos in
    if f c
    then eval_success input (pos + 1) more c succ
    else eval_failure input pos more [] "satisfy" fail

and eval_failure :
  type r. (string list -> string -> r failure -> r state) with_state =
  fun input pos more marks msg -> function
  | Fail_fail -> Fail(pos - Input.client_committed_bytes input, marks, msg)
  | Fail_mark(mark, fail) -> eval_failure input pos more (mark::marks) msg fail
  | Fail_choice(old_pos, old_more, p, fail, succ) ->
      (* The only two constructors that introduce new failure continuations are
       * [<?>] and [<|>]. If the initial input position is less than the length
       * of the committed input, then calling the failure continuation will
       * have the effect of unwinding all choices and collecting marks along
       * the way. *)
      if old_pos < Input.parser_committed_bytes input then
        eval_failure input pos old_more marks msg fail
      else
        eval input old_pos more fail succ p

and eval_continue input ~off ~len more = function
  | Continue { parser_uncommitted_bytes; parser_committed_bytes;
              pos; resume; complete; succ; fail; _ } ->
    if len < parser_uncommitted_bytes then
      failwith "prompt: input shrunk!";
    let input = Input.create input ~off ~len ~committed_bytes:parser_committed_bytes in
    if len = parser_uncommitted_bytes then
      match (more : More.t) with
      | Complete   -> eval input pos More.Complete fail succ complete
      | Incomplete -> prompt input pos resume complete fail succ
    else
      eval input pos more fail succ resume

let parse p =
  let input = Input.create Bigstringaf.empty ~committed_bytes:0 ~off:0 ~len:0 in
  eval input 0 Incomplete Fail_fail Succ_done p

let parse_bigstring p input =
  let input =
    Input.create input ~committed_bytes:0 ~off:0 ~len:(Bigstringaf.length input)
  in
  state_to_result (eval input 0 Complete Fail_fail Succ_done p)

module Monad = struct
  let return v = Return v

  let fail msg = Failure msg

  let (>>=) p f = Bind(p, f)

  let (>>|) p f = Map(p, f)

  let (<$>) f m =
    m >>| f

  let (<*>) f m = App(f, m)

  let lift f m =
    f <$> m

  let lift2 f m1 m2 = Map2(m1, m2, f)

  let lift3 f m1 m2 m3 = Map3(m1, m2, m3, f)

  let lift4 f m1 m2 m3 m4 = Map4(m1, m2, m3, m4, f)

  let ( *>) a b = Seq_right(a, b)

  let (<* ) a b = Seq_left(a, b)
end

module Choice = struct
  let (<?>) p mark = Mark(p, mark)

  let (<|>) p q = Choice(p, q)
end

let fix f =
  let rec p = lazy (f r)
  and r = Lazy p in
  r

module Monad_use_for_debugging = struct
  let return = Monad.return
  let fail   = Monad.fail
  let (>>=)  = Monad.(>>=)

  let (>>|) m f = m >>= fun x -> return (f x)

  let (<$>) f m = m >>| f
  let (<*>) f m = f >>= fun f -> m >>| f

  let lift  = (>>|)
  let lift2 f m1 m2       = f <$> m1 <*> m2
  let lift3 f m1 m2 m3    = f <$> m1 <*> m2 <*> m3
  let lift4 f m1 m2 m3 m4 = f <$> m1 <*> m2 <*> m3 <*> m4

  let ( *>) a b = a >>= fun _ -> b
  let (<* ) a b = a >>= fun x -> b >>| fun _ -> x
end
