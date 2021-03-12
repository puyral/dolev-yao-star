module AttackerAPI

let query_result (idx_state:nat) (p:principal) (si:nat) (sv:nat) (res:bytes) : Type0 =
  (exists ver_vec state.
    state_was_set_at idx_state p ver_vec state /\
    Seq.length ver_vec = Seq.length state /\
    Seq.length ver_vec > si /\
    Seq.index ver_vec si = sv /\
    Seq.index state si == res)

let rec attacker_can_derive (i:nat) (steps:nat) (t:bytes):
                         Tot Type0 (decreases steps) =
  if steps = 0 then
    (* Attacker can read terms that were published (i.e., messages sent by someone in the past) *)
     ((i > 0 /\ was_published_before (i-1) t) \/
    (* Attacker can read the state of corrupted principals *)
      (exists idx_state sess_idx sess_ver corrupted_principal.
        idx_state < i /\
	query_result idx_state corrupted_principal sess_idx sess_ver t /\
        was_corrupted_before i corrupted_principal sess_idx sess_ver) \/
    (* Attacker can call from_pub_bytes, i.e., can derive constants *)
      (exists (s:literal). t == literal_to_bytes s))
  else (
      // Just reduce steps by one
      (attacker_can_derive i (steps - 1) t) \/
      // Attacker can concatenate bytes
      (exists (t1 t2:bytes).
        t == concat t1 t2 /\
        attacker_can_derive i (steps - 1) t1 /\
        attacker_can_derive i (steps - 1) t2) \/
      // Attacker can construct public key from private key
      (exists (priv_key:bytes).
        t == pk priv_key /\
        attacker_can_derive i (steps - 1) priv_key) \/
      // Asymmetric encryption
      (exists (t1 t2:bytes).
        t == pke_enc t1 t2 /\
        attacker_can_derive i (steps - 1) t1 /\
        attacker_can_derive i (steps - 1) t2) \/
      // Symmetric encryption
      (exists (t1 t2 t3:bytes).
        t == aead_enc t1 t2 t3 /\
        attacker_can_derive i (steps - 1) t1 /\
        attacker_can_derive i (steps - 1) t2 /\
        attacker_can_derive i (steps - 1) t3) \/
      // Create signatures
      (exists (t1 t2:bytes).
        t == sign t1 t2 /\
        attacker_can_derive i (steps - 1) t1 /\
        attacker_can_derive i (steps - 1) t2) \/
      // Create macs
      (exists (t1 t2:bytes).
        t == mac t1 t2 /\
        attacker_can_derive i (steps - 1) t1 /\
        attacker_can_derive i (steps - 1) t2) \/
      // Create hashes
      (exists t1.
        t == hash t1 /\
        attacker_can_derive i (steps - 1) t1) \/
      // Attacker can derive new keys from a key and a context
      (exists (t1 t2:bytes).
        t == extract t1 t2 /\
        attacker_can_derive i (steps - 1) t1 /\
        attacker_can_derive i (steps - 1) t2) \/
      (exists (t1:bytes) (t2:bytes).
        t == expand t1 t2 /\
        attacker_can_derive i (steps - 1) t1 /\
	attacker_can_derive i (steps - 1) t2) \/
      // Split up concatenated bytes
      (exists (t1 t2:bytes).
        is_succ2 (split t1) t t2 /\
        attacker_can_derive i (steps - 1) t1) \/
      (exists (t1 t2:bytes).
         is_succ2 (split t1) t2 t /\
        attacker_can_derive i (steps - 1) t1) \/
      // Asymmetric decryption
      (exists (t1 t2:bytes).
        is_succ (pke_dec t1 t2) t /\
        attacker_can_derive i (steps - 1) t1 /\
        attacker_can_derive i (steps - 1) t2) \/
      // Symmetric decryption
      (exists (t1 t2 t3:bytes).
        is_succ (aead_dec t1 t2 t3) t /\
        attacker_can_derive i (steps - 1) t1 /\
        attacker_can_derive i (steps - 1) t2 /\
        attacker_can_derive i (steps - 1) t3) \/
      // DH
      (exists (t1 t2:bytes).
        t == (dh t1 (dh_pk t2)) /\
        attacker_can_derive i (steps - 1) t1 /\
        attacker_can_derive i (steps - 1) t2))

let attacker_can_query_compromised_state idx_state idx_corrupt idx_query principal si sv res =
  assert (query_result idx_state principal si sv res);
  assert (query_result idx_state principal si sv res)

let rec attacker_can_derive_in_more_steps i steps1 steps2 =
  if steps2 = 0 then ()
  else if steps1 = steps2 then ()
       else (attacker_can_derive_in_more_steps i steps1 (steps2 - 1))

#push-options "--z3rlimit 50"
let rec attacker_can_derive_later i steps j =
  if steps = 0 then ()
  else (attacker_can_derive_later i (steps - 1) j)
#pop-options

let attacker_knows_later i j =
  let attacker_knows_later_steps (steps:nat) (a:bytes):
    Lemma (ensures (attacker_can_derive i steps a ==> attacker_can_derive j steps a))
          [SMTPat (attacker_can_derive i steps a); SMTPat (attacker_can_derive j steps a)] =
          attacker_can_derive_later i steps j in
  ()

let literal_to_pub_bytes l : pub_bytes 0 =
  let t = literal_to_bytes l in
  assert (attacker_can_derive 0 0 t);
  assert (attacker_knows_at 0 t);
  t

let literal_to_pub_bytes_lemma l = ()

let pub_bytes_to_literal #i t = bytes_to_literal t 
let pub_bytes_to_literal_lemma #i p = ()

let max a b = if a < b then b else a

val meet_derives: i:nat -> j:nat -> steps1:nat -> steps2:nat -> t1:bytes -> t2:bytes ->
  Lemma (requires (attacker_can_derive i steps1 t1 /\ attacker_can_derive j steps2 t2))
        (ensures (attacker_can_derive (max i j) (max steps1 steps2) t1 /\
                  attacker_can_derive (max i j) (max steps1 steps2) t2))
let meet_derives i j steps1 steps2 t1 t2 =
  (if steps1 < steps2 then
    attacker_can_derive_in_more_steps i steps1 steps2
   else
    attacker_can_derive_in_more_steps j steps2 steps1);
  (if i < j then
    attacker_can_derive_later i (max steps1 steps2) j
   else
    attacker_can_derive_later j (max steps1 steps2) i);
   assert (attacker_can_derive (max i j) (max steps1 steps2) t1);
   assert (attacker_can_derive (max i j) (max steps1 steps2) t2)

val meet_derives3: i:nat -> j:nat -> k:nat -> steps1:nat -> steps2:nat -> steps3:nat -> t1:bytes -> t2:bytes -> t3:bytes ->
  Lemma (requires (attacker_can_derive i steps1 t1 /\ attacker_can_derive j steps2 t2 /\ attacker_can_derive k steps3 t3))
	(ensures (attacker_can_derive (max (max i j) k) (max (max steps1 steps2) steps3) t1 /\
                  attacker_can_derive (max (max i j) k) (max (max steps1 steps2) steps3) t2 /\
                  attacker_can_derive (max (max i j) k) (max (max steps1 steps2) steps3) t3))
let meet_derives3 i j k steps1 steps2 steps3 t1 t2 t3 =
  meet_derives i j steps1 steps2 t1 t2;
  meet_derives (max i j) k (max steps1 steps2) steps3 t1 t3;
  meet_derives (max i j) k (max steps1 steps2) steps3 t2 t3


(* Concatenate and split bytestrings *)
let incr a  = a + 1

#set-options "--z3rlimit 50 --max_fuel 1 --max_ifuel 1"
let concat #i t1 t2 =
  let concat_pub_lemma0 (i:nat) (t1:bytes) (t2:bytes) (steps:nat) :
  Lemma (requires (attacker_can_derive i steps t1 /\ attacker_can_derive i steps t2))
        (ensures (attacker_can_derive i (steps + 1) (concat t1 t2)))
        [SMTPat (attacker_can_derive i steps t1); SMTPat (attacker_can_derive i steps t2)] =
        () in
  let concat_pub_lemma (i:nat) (j:nat) (t1:bytes) (t2:bytes) (steps1:nat) (steps2:nat) :
  Lemma (requires (attacker_can_derive i steps1 t1 /\ attacker_can_derive j steps2 t2))
        (ensures (attacker_can_derive (max i j) (max steps1 steps2 + 1) (concat t1 t2)))
        [SMTPat (attacker_can_derive i steps1 t1); SMTPat (attacker_can_derive j steps2 t2)] =
        meet_derives i j steps1 steps2 t1 t2;
        assert (attacker_can_derive (max i j) (max steps1 steps2 + 1) (concat t1 t2));
   () in
let c = concat t1 t2 in
c

let concat_lemma #i t1 t2 = ()

let split #i t =
  let split_pub_lemma1 (i:nat) (a1:bytes) (a:bytes) (a2:bytes) (steps:nat) :
  Lemma (requires (attacker_can_derive i steps a1 /\ is_succ2 (split a1) a a2))
        (ensures (attacker_can_derive i (steps + 1) a))
        [SMTPat (attacker_can_derive i steps a1); SMTPat (is_succ2 (split a1) a a2)] =  () in
  let split_pub_lemma2 (i:nat) (a1:bytes) (a:bytes) (a2:bytes) (steps:nat) :
  Lemma (requires (attacker_can_derive i steps a1 /\ is_succ2 (split a1) a2 a))
        (ensures (attacker_can_derive i (steps + 1) a))
        [SMTPat (attacker_can_derive i steps a1); SMTPat (is_succ2 (split a1) a2 a)] =  () in
  let b = split t in
  match b with
  | Success (a1,a2) -> (
    assert (is_succ2 (split t) a1 a2);
    let p1:pub_bytes i = a1 in
    let p2:pub_bytes i = a2 in
    assert (split t == Success (a1,a2));
    Success (a1,a2))
  | Error s -> (assert (match split t with | Error s -> True | Success _ -> False); Error s)
let split_lemma #i t = ()

(* Public key corresponding to a secret key *)
let pk #i k =
  let pk_pub_lemma (i:nat) (s:bytes) (steps:nat) :
  Lemma (requires (attacker_can_derive i steps s))
        (ensures (attacker_can_derive i (steps + 1) (pk s)))
        [SMTPat (attacker_can_derive i steps s)] = () in
  pk k
let pk_lemma #i s = ()

(* Public key encryption *)
let pke_enc #i t1 t2 =
  let pke_enc_pub_lemma0 (i:nat) (t1:bytes) (t2:bytes) (steps:nat) :
  Lemma (requires (attacker_can_derive i steps t1 /\ attacker_can_derive i steps t2))
        (ensures (attacker_can_derive i (steps + 1) (pke_enc t1 t2)))
        [SMTPat (attacker_can_derive i steps t1); SMTPat (attacker_can_derive i steps t2)] = () in
  let pke_enc_pub_lemma (i:nat) (j:nat) (t1:bytes) (t2:bytes) (steps1:nat) (steps2:nat) :
  Lemma (requires (attacker_can_derive i steps1 t1 /\ attacker_can_derive j steps2 t2))
        (ensures (attacker_can_derive (max i j) (max steps1 steps2 + 1) (pke_enc t1 t2)))
        [SMTPat (attacker_can_derive i steps1 t1); SMTPat (attacker_can_derive j steps2 t2)] =
        meet_derives i j steps1 steps2 t1 t2;
        assert (attacker_can_derive (max i j) (max steps1 steps2 + 1) (pke_enc t1 t2)) in
  pke_enc t1 t2
let pke_enc_lemma #i t1 t2 = ()

let pke_dec #i k e =
  let pke_dec_pub_lemma0 (i:nat) (k:bytes) (e:bytes) (p:bytes) (steps:nat):
  Lemma (requires (attacker_can_derive i steps k /\
                   attacker_can_derive i steps e /\
                   is_succ (pke_dec k e) p))
        (ensures (attacker_can_derive i (steps + 1) p))
        [SMTPat (attacker_can_derive i steps k);
         SMTPat (attacker_can_derive i steps e);
         SMTPat (is_succ (pke_dec k e) p)] = () in
  let pke_dec_pub_lemma (i:nat) (j:nat) (k:bytes) (e:bytes) (p:bytes) (steps1:nat) (steps2:nat):
  Lemma (requires (attacker_can_derive i steps1 k /\
                   attacker_can_derive j steps2 e /\
                   is_succ (pke_dec k e) p))
        (ensures (attacker_can_derive (max i j) (max steps1 steps2 + 1) p))
        [SMTPat (attacker_can_derive i steps1 k);
         SMTPat (attacker_can_derive j steps2 e);
         SMTPat (is_succ (pke_dec k e) p)] =
         meet_derives i j steps1 steps2 k e;
         assert (attacker_can_derive (max i j) (max steps1 steps2 + 1) p) in
  match pke_dec k e with
  | Success p -> Success p
  | Error s -> Error s

let pke_dec_lemma #i t1 t2 = ()

let aead_enc #i t1 t2 t3 =
  let aead_enc_pub_lemma0 (i:nat) (t1:bytes) (t2:bytes) (t3:bytes) (steps:nat) :
  Lemma (requires (attacker_can_derive i steps t1 /\ attacker_can_derive i steps t2 /\ attacker_can_derive i steps t3))
        (ensures (attacker_can_derive i (steps + 1) (aead_enc t1 t2 t3)))
        [SMTPat (attacker_can_derive i steps t1); SMTPat (attacker_can_derive i steps t2); SMTPat (attacker_can_derive i steps t3)] = () in
  let aead_enc_pub_lemma (i:nat) (t1:bytes) (t2:bytes) (t3:bytes)  (steps1:nat) (steps2:nat) (steps3:nat):
  Lemma (requires (attacker_can_derive i steps1 t1 /\ attacker_can_derive i steps2 t2 /\ attacker_can_derive i steps3 t3))
        (ensures (attacker_knows_at i (aead_enc t1 t2 t3)))
        [SMTPat (attacker_can_derive i steps1 t1); SMTPat (attacker_can_derive i steps2 t2); SMTPat (attacker_can_derive i steps3 t3)] =
        meet_derives3 i i i steps1 steps2 steps3 t1 t2 t3;
	() in
   let res = aead_enc t1 t2 t3 in
   res


let aead_enc_lemma #i t1 t2 t3 = ()


let aead_dec #i k e ad =
  let aead_dec_pub_lemma0 (i:nat) (k:bytes) (e:bytes) (p:bytes) (ad:bytes) (steps:nat) :
  Lemma (requires (attacker_can_derive i steps k /\
                   attacker_can_derive i steps e /\
                   attacker_can_derive i steps ad /\
                   is_succ (aead_dec k e ad) p))
        (ensures (attacker_can_derive i (steps + 1) p))
        [SMTPat (attacker_can_derive i steps k);
         SMTPat (attacker_can_derive i steps e);
         SMTPat (attacker_can_derive i steps ad);
         SMTPat (is_succ (aead_dec k e ad) p)] = () in
  let aead_dec_pub_lemma (i:nat) (e:bytes) (p:bytes) (ad:bytes) (steps1:nat) (steps2:nat) (steps3:nat):
  Lemma (requires (attacker_can_derive i steps1 k /\
                   attacker_can_derive i steps2 e /\
                   attacker_can_derive i steps3 ad /\
                   is_succ (aead_dec k e ad) p))
        (ensures (attacker_knows_at i p))
        [SMTPat (attacker_can_derive i steps1 k);
         SMTPat (attacker_can_derive i steps2 e);
         SMTPat (attacker_can_derive i steps3 ad);
         SMTPat (is_succ (aead_dec k e ad) p)] =
         meet_derives3 i i i steps1 steps2 steps3 k e ad in
  match aead_dec k e ad with
  | Success p ->
    assert (is_succ (aead_dec k e ad) p);
    let p:pub_bytes i = p in
    Success p
  | Error s -> Error s
let aead_dec_lemma #i t1 t2 t3 = ()

let sign #i t1 t2 =
  let sign_pub_lemma0 (i:nat) (t1:bytes) (t2:bytes) (steps:nat) :
  Lemma (requires (attacker_can_derive i steps t1 /\ attacker_can_derive i steps t2))
        (ensures (attacker_can_derive i (steps + 1) (sign t1 t2)))
         = () in
  let sign_pub_lemma (i:nat) (j:nat) (t1:bytes) (t2:bytes) (steps1:nat) (steps2:nat) :
  Lemma (requires (attacker_can_derive i steps1 t1 /\ attacker_can_derive j steps2 t2))
        (ensures (attacker_can_derive (max i j) (max steps1 steps2 + 1) (sign t1 t2)))
        [SMTPat (attacker_can_derive i steps1 t1); SMTPat (attacker_can_derive j steps2 t2)] =
        meet_derives i j steps1 steps2 t1 t2;
        sign_pub_lemma0 (max i j) t1 t2 (max steps1 steps2) in
  sign t1 t2

let sign_lemma #i t1 t2 = ()

let verify #i t1 t2 t3 = verify t1 t2 t3
let verify_lemma #i t1 t2 t3 = ()

let mac #i t1 t2 =
  let mac_pub_lemma0 (i:nat) (t1:bytes) (t2:bytes) (steps:nat) :
  Lemma (requires (attacker_can_derive i steps t1 /\ attacker_can_derive i steps t2))
        (ensures (attacker_can_derive i (steps + 1) (mac t1 t2)))
         = () in
  let mac_pub_lemma (i:nat) (j:nat) (t1:bytes) (t2:bytes) (steps1:nat) (steps2:nat) :
  Lemma (requires (attacker_can_derive i steps1 t1 /\ attacker_can_derive j steps2 t2))
        (ensures (attacker_can_derive (max i j) (max steps1 steps2 + 1) (mac t1 t2)))
        [SMTPat (attacker_can_derive i steps1 t1); SMTPat (attacker_can_derive j steps2 t2)] =
        meet_derives i j steps1 steps2 t1 t2;
        mac_pub_lemma0 (max i j) t1 t2 (max steps1 steps2) in
  mac t1 t2
let mac_lemma #i t1 t2 = ()

let verify_mac #i t1 t2 t3 = verify_mac t1 t2 t3
let verify_mac_lemma #i t1 t2 t3 = ()

let hash #i t1 =
  let hash_pub_lemma0 (i:nat) (t1:bytes) (steps:nat) :
  Lemma (requires (attacker_can_derive i steps t1))
        (ensures (attacker_can_derive i (steps + 1) (hash t1)))
         = () in
  let hash_pub_lemma (i:nat) (t1:bytes) (steps1:nat):
  Lemma (requires (attacker_can_derive i steps1 t1))
        (ensures (attacker_can_derive i (steps1 + 1) (hash t1)))
        [SMTPat (attacker_can_derive i steps1 t1)] =
        hash_pub_lemma0 i t1 steps1 in
  hash t1
let hash_lemma #i t1 = ()

let global_timestamp () = global_timestamp ()

#push-options "--max_ifuel 2 --z3rlimit 200"
let pub_rand_gen u =
  let t0 = get () in
  let n = gen public u in
  let t1 = get() in
  let i = send "*" "*" n in
  let t2 = get() in
  assert (was_published_at (trace_len t0 + 1) n);
  assert (was_published_before (trace_len t0 + 1) n);
  assert (attacker_can_derive (trace_len t0+2) 0 n);
  let i = global_timestamp () in
  assert (i == trace_len  t2);
  (|i, n|)

let send #i p1 p2 a = send p1 p2 a

let receive_i i p2 =
  let (_,m) = receive_i i p2 in
  let n = global_timestamp () in
  assert (was_published_at i m);
  assert (was_published_before i m);
  assert (attacker_can_derive (i+1) 0 m);
  assert (attacker_knows_at (i+1) m);
  let m' : pub_bytes (i+1) = m in
  (| n, m |)

let compromise p s v =
  let n = global_timestamp () in
  compromise p s v;
  n

let query_state_i idx_state idx_corrupt idx_query p si sv =
  let (v,s) = get_state_i idx_state p in
  assert (state_was_set_at idx_state p v s);
  if Seq.length v <= si || Seq.index v si <> sv || Seq.length s <> Seq.length v
  then error "cannot query state"
  else
    let n = global_timestamp () in
    let res = s.[si] in
    attacker_can_query_compromised_state idx_state idx_corrupt idx_query p si sv res;
    res

