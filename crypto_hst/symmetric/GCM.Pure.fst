module GCM.Pure

open FStar.Mul
open FStar.Seq
open FStar.UInt8

module U32 = FStar.UInt32
type u32 = FStar.UInt32.t
type u8s = seq FStar.UInt8.t

assume val maxvalue: n:nat{n < 256} -> Lemma (n < pow2 8 /\ n < pow2 32)

(* Define a type for all 16-byte block cipher algorithm *)
type cipher_alg (k: pos) = key:u8s{length key = k} ->
    input:u8s{length input = 16} ->
    Tot (out:u8s{length out = 16})

private val gf128_add_loop: a:u8s{length a = 16} ->
    b:u8s{length b = 16} ->
    dep:nat{dep <= 16} ->
    Tot (res:u8s{length res = 16})
    (decreases dep)
let rec gf128_add_loop a b dep =
  if dep = 0 then a else begin
    let i = dep - 1 in
    let ai = index a i in
    let bi = index b i in
    let x = logxor ai bi in
    let na = upd a i x in
    gf128_add_loop na b i
  end

val gf128_add: a:u8s{length a = 16} ->
    b:u8s{length b = 16} ->
    Tot (res:u8s{length res = 16})
let gf128_add a b = gf128_add_loop a b 16

private val gf128_shift_right_loop: a:u8s{length a = 16} ->
    dep:nat{dep < 16} ->
    Tot (res:u8s{length res = 16})
    (decreases dep)
let rec gf128_shift_right_loop a dep =
  if dep = 0 then begin
    let ai = index a 0 in
    let x = shift_right ai 1ul in
    upd a 0 x
  end else begin
    let i = dep - 1 in
    let hd = index a i in
    let tl = index a dep in
    maxvalue 7;
    Math.Lemmas.pow2_multiplication_modulo_lemma_2 (v hd) 8 7;
    let x = add (shift_left hd 7ul) (shift_right tl 1ul) in
    let na = upd a dep x in
    gf128_shift_right_loop na i
  end

private val gf128_shift_right: a:u8s{length a = 16} ->
    Tot (res:u8s{length res = 16})
let gf128_shift_right a = gf128_shift_right_loop a 15

(* The rest havn't been translated to Pure version. *)

(*
private val ith_bit_mask: num:byte -> i:u32{U32.v i < 8} -> Tot byte
let ith_bit_mask num i =
  maxvalue 128;
  let proj = shift_right 128uy i in
  let res = logand num proj in
  eq_mask res proj

private val apply_mask_loop: a:u8s{length a = 16} ->
    m:u8s{length m = 16} ->
    msk:byte -> dep:nat{dep <= 16} -> 
    Tot (res:u8s{length res = 16})
    (decreases dep)
let rec apply_mask_loop a m msk dep =
  if dep = 0 then m else begin
    let i = dep - 1 in
    let ai = index a i in
    let x = logand ai msk in
    let nm = upd m i x in
    apply_mask_loop a nm msk i
  end

private val apply_mask: a:u8s{length a = 16} ->
    m:u8s{length m = 16} ->
    msk:byte -> Tot (res:u8s{length res = 16})
let apply_mask a m msk = apply_mask_loop a m msk 16

private val r_mul: byte
let r_mul = 225uy

private val gf128_mul_loop: a:u8s{length a = 16} ->
    b:u8s{length b = 16} ->
    tmp:u8s{length tmp = 32} ->
    dep:nat{dep <= 128} ->
    Tot (res:u8s{length res = 16})
    (decreases (128 - dep))
let rec gf128_mul_loop a b tmp dep =
  if dep = 128 then a else begin
    let r = slice tmp 0 16 in
    let m = slice tmp 16 16 in
    let num = index b (dep / 8) in
    let msk = ith_bit_mask num (FStar.UInt32.Mk (dep % 8)) in
    let m = apply_mask a m msk in
    let r = gf128_add r m in
    let num = index a 15 in
    let msk = ith_bit_mask num 7ul in
    let na = gf128_shift_right a in
    let num = index na 0 in
    let na = upd na 0 (logxor num (logand msk r_mul)) in
    gf128_mul_loop na b tmp (dep + 1)
  end
  
val gf128_mul: a:u8s{length a = 16} ->
    b:u8s{length b = 16 /\ disjoint a b} -> STL unit
    (requires (fun h -> live h a /\ live h b))
    (ensures (fun h0 _ h1 -> live h1 a /\ live h1 b /\ modifies_1 a h0 h1))
let gf128_mul a b =
  push_frame();
  let tmp = create (uint8_to_sint8 0uy) 32ul in
  gf128_mul_loop a b tmp 0ul;
  blit tmp 0ul a 0ul 16ul;
  pop_frame()
  
private val mk_len_info: len_info:u8s{length len_info = 16} ->
    len_1:u32 -> len_2:u32 -> STL unit
    (requires (fun h -> live h len_info))
    (ensures (fun h0 _ h1 -> live h1 len_info /\ modifies_1 len_info h0 h1))
let mk_len_info len_info len_1 len_2 =
  let last = shift_left (uint32_to_sint8 len_1) 3ul in
  upd len_info 7ul last;
  let len_1 = U32.shift_right len_1 5ul in
  upd len_info 6ul (uint32_to_sint8 len_1);
  let len_1 = U32.shift_right len_1 8ul in
  upd len_info 5ul (uint32_to_sint8 len_1);
  let len_1 = U32.shift_right len_1 8ul in
  upd len_info 4ul (uint32_to_sint8 len_1);
  let len_1 = U32.shift_right len_1 8ul in
  upd len_info 3ul (uint32_to_sint8 len_1);
  let last = shift_left (uint32_to_sint8 len_2) 3ul in
  upd len_info 15ul last;
  let len_2 = U32.shift_right len_2 5ul in
  upd len_info 14ul (uint32_to_sint8 len_2);
  let len_2 = U32.shift_right len_2 8ul in
  upd len_info 13ul (uint32_to_sint8 len_2);
  let len_2 = U32.shift_right len_2 8ul in
  upd len_info 12ul (uint32_to_sint8 len_2);
  let len_2 = U32.shift_right len_2 8ul in
  upd len_info 11ul (uint32_to_sint8 len_2)

private val ghash_loop: tag:u8s{length tag = 16} ->
    auth_key:u8s{length auth_key = 16 /\ disjoint tag auth_key} ->
    str:u8s{disjoint tag str /\ disjoint auth_key tag} ->
    len:u32{length str = U32.v len} ->
    dep:u32{U32.v dep <= U32.v len} -> STL unit
    (requires (fun h -> live h tag /\ live h auth_key /\ live h str))
    (ensures (fun h0 _ h1 -> live h1 tag /\ live h1 auth_key /\ live h1 str /\ modifies_1 tag h0 h1))
let rec ghash_loop tag auth_key str len dep =
  if U32.gte 16ul (U32.sub len dep) then begin
    push_frame();
    let last = create (uint8_to_sint8 0uy) 16ul in
    blit str dep last 0ul (U32.sub len dep);
    gf128_add tag last;
    gf128_mul tag auth_key;
    pop_frame()
  end else begin
    let next = U32.add dep 16ul in
    let si = sub str dep 16ul in
    gf128_add tag si;
    gf128_mul tag auth_key;
    ghash_loop tag auth_key str len next
  end

val ghash: auth_key:u8s{length auth_key = 16} ->
    ad:u8s{disjoint auth_key ad} ->
    adlen:u32{U32.v adlen = length ad} ->
    ciphertext:u8s{disjoint auth_key ciphertext /\ disjoint ad ciphertext} ->
    len:u32{U32.v len = length ciphertext} ->
    tag:u8s{length tag = 16 /\ disjoint auth_key tag /\ disjoint ad tag /\ disjoint ciphertext tag} ->
    STL unit
    (requires (fun h -> live h auth_key /\ live h ad /\ live h ciphertext /\ live h tag))
    (ensures (fun h0 _ h1 -> live h1 auth_key /\ live h1 ad /\ live h1 ciphertext /\ live h1 tag
        /\ modifies_1 tag h0 h1))
let ghash auth_key ad adlen ciphertext len tag =
  fill tag (uint8_to_sint8 0uy) 16ul;
  ghash_loop tag auth_key ad adlen 0ul;
  ghash_loop tag auth_key ciphertext len 0ul;
  push_frame();
  let len_info = create (uint8_to_sint8 0uy) 16ul in
  mk_len_info len_info adlen len;
  gf128_add tag len_info;
  gf128_mul tag auth_key;
  pop_frame()

private val update_counter: counter:u8s{length counter = 16} ->
    num:u32 -> STL unit
    (requires (fun h -> live h counter))
    (ensures (fun h0 _ h1 -> live h1 counter /\ modifies_1 counter h0 h1))
let update_counter counter num =
  upd counter 15ul (uint32_to_sint8 num);
  let num = U32.shift_right num 8ul in
  upd counter 14ul (uint32_to_sint8 num);
  let num = U32.shift_right num 8ul in
  upd counter 13ul (uint32_to_sint8 num);
  let num = U32.shift_right num 8ul in
  upd counter 12ul (uint32_to_sint8 num)

private val auth_body: #k:pos -> alg:cipher_alg k ->
    ciphertext:u8s ->
    tag:u8s{length tag = 16 /\ disjoint ciphertext tag} ->
    key:u8s{length key = k /\ disjoint key ciphertext /\ disjoint tag key} ->
    nonce:u8s{length nonce = 12 /\ disjoint ciphertext nonce /\ disjoint tag nonce /\ disjoint key nonce} ->
    cnt:u32 ->
    ad:u8s{disjoint ciphertext ad /\ disjoint tag ad /\ disjoint key ad /\ disjoint nonce ad} ->
    adlen:u32{length ad = U32.v adlen} ->
    len:u32{length ciphertext = U32.v len} ->
    tmp:u8s{length tmp = 48 /\ disjoint ciphertext tmp /\ disjoint tag tmp /\ disjoint key tmp /\ disjoint nonce tmp /\ disjoint ad tmp} ->
    STL unit
    (requires (fun h -> live h ciphertext /\ live h tag /\ live h key /\ live h nonce /\ live h ad /\ live h tmp))
    (ensures (fun h0 _ h1 -> live h1 ciphertext /\ live h1 tag /\ live h1 key /\ live h1 nonce /\ live h1 ad /\ live h1 tmp
        /\ modifies_2 tag tmp h0 h1))
let auth_body #k alg ciphertext tag key nonce cnt ad adlen len tmp =
  let h0 = HST.get() in
  fill tag (uint8_to_sint8 0uy) 16ul;
  let auth_key = sub tmp 0ul 16ul in
  alg key tag auth_key;
  ghash auth_key ad adlen ciphertext len tag;
  let counter = sub tmp 16ul 16ul in
  blit nonce 0ul counter 0ul 12ul;
  update_counter counter cnt;
  let c0 = sub tmp 32ul 16ul in
  alg key counter c0;
  gf128_add tag c0;
  let h1 = HST.get() in
  assert(live h1 ciphertext /\ live h1 tag /\ live h1 key /\ live h1 nonce /\ live h1 ad /\ live h1 tmp /\ modifies_2 tag tmp h0 h1)

private val authenticate: #k:pos -> alg:cipher_alg k ->
    ciphertext:u8s ->
    tag:u8s{length tag = 16 /\ disjoint ciphertext tag} ->
    key:u8s{length key = k /\ disjoint ciphertext key /\ disjoint tag key} ->
    nonce:u8s{length nonce = 12 /\ disjoint ciphertext nonce /\ disjoint tag nonce /\ disjoint key nonce} ->
    cnt:u32 ->
    ad:u8s{disjoint ciphertext ad /\ disjoint tag ad /\ disjoint key ad /\ disjoint nonce ad} ->
    adlen:u32{length ad = U32.v adlen} ->
    len:u32{length ciphertext = U32.v len} ->
    STL unit
    (requires (fun h -> live h ciphertext /\ live h tag /\ live h key /\ live h nonce /\ live h ad))
    (ensures (fun h0 _ h1 -> live h1 ciphertext /\ live h1 tag /\ live h1 key /\ live h1 nonce /\ live h1 ad
        /\ modifies_1 tag h0 h1))
let authenticate #k alg ciphertext tag key nonce cnt ad adlen len =
  push_frame();
  let tmp = create (uint8_to_sint8 0uy) 48ul in
  auth_body #k alg ciphertext tag key nonce cnt ad adlen len tmp;
  pop_frame()

private val encrypt_loop: #k:pos -> alg:cipher_alg k ->
    ciphertext:u8s ->
    key:u8s{length key = k /\ disjoint ciphertext key} ->
    cnt:u32 ->
    plaintext:u8s{length plaintext = length ciphertext /\ disjoint ciphertext plaintext /\ disjoint key plaintext} ->
    len:u32{length ciphertext = U32.v len} ->
    tmp:u8s{length tmp = 48 /\ disjoint ciphertext tmp /\ disjoint key tmp /\ disjoint plaintext tmp} ->
    dep:u32{U32.v dep <= U32.v len} ->
    STL unit
    (requires (fun h -> live h ciphertext /\ live h key /\ live h plaintext /\ live h tmp))
    (ensures (fun h0 _ h1 -> live h1 ciphertext /\ live h1 key /\ live h1 plaintext /\ live h1 tmp
        /\ modifies_2 ciphertext tmp h0 h1))
let rec encrypt_loop #k alg ciphertext key cnt plaintext len tmp dep =
  if U32.gte 16ul (U32.sub len dep) then begin
    let h0 = HST.get() in
    let counter = sub tmp 0ul 16ul in
    update_counter counter cnt;
    let last = sub tmp 16ul 16ul in
    blit plaintext dep last 0ul (U32.sub len dep);
    let ci = sub tmp 32ul 16ul in
    alg key counter ci;
    gf128_add ci last;
    blit ci 0ul ciphertext dep (U32.sub len dep);
    let h1 = HST.get() in
    assert(live h1 ciphertext /\ live h1 key /\ live h1 plaintext /\ live h1 tmp /\ modifies_2 ciphertext tmp h0 h1)
  end else begin
    let h0 = HST.get() in
    let pi = sub plaintext dep 16ul in
    let counter = sub tmp 0ul 16ul in
    update_counter counter cnt;
    let ci = sub ciphertext dep 16ul in
    alg key counter ci;
    gf128_add ci pi;
    encrypt_loop #k alg ciphertext key (U32.add_mod cnt 1ul) plaintext len tmp (U32.add dep 16ul);
    let h1 = HST.get() in
    assert(live h1 ciphertext /\ live h1 key /\ live h1 plaintext /\ live h1 tmp /\ modifies_2 ciphertext tmp h0 h1)
  end

private val encrypt_body: #k:pos -> alg:cipher_alg k ->
    ciphertext:u8s ->
    tag:u8s{length tag = 16 /\ disjoint ciphertext tag} ->
    key:u8s{length key = k /\ disjoint ciphertext key /\ disjoint tag key} ->
    nonce:u8s{length nonce = 12 /\ disjoint ciphertext nonce /\ disjoint tag nonce /\ disjoint key nonce} ->
    cnt:u32 ->
    ad:u8s{disjoint ciphertext ad /\ disjoint tag ad /\ disjoint key ad /\ disjoint nonce ad} ->
    adlen:u32{length ad = U32.v adlen} ->
    plaintext:u8s{length plaintext = length ciphertext /\ disjoint ciphertext plaintext /\ disjoint tag plaintext /\ disjoint key plaintext /\ disjoint nonce plaintext /\ disjoint ad plaintext} ->
    len:u32{length ciphertext = U32.v len} ->
    STL unit
    (requires (fun h -> live h ciphertext /\ live h tag /\ live h key /\ live h nonce /\ live h ad /\ live h plaintext))
    (ensures (fun h0 _ h1 -> live h1 ciphertext /\ live h1 tag /\ live h1 key /\ live h1 nonce /\ live h1 ad /\ live h1 plaintext
        /\ modifies_2 ciphertext tag h0 h1))
let encrypt_body #k alg ciphertext tag key nonce cnt ad adlen plaintext len =
  push_frame();
  let tmp = create (uint8_to_sint8 0uy) 48ul in
  blit nonce 0ul tmp 0ul 12ul;
  encrypt_loop #k alg ciphertext key (U32.add_mod cnt 1ul) plaintext len tmp 0ul;
  pop_frame();
  authenticate #k alg ciphertext tag key nonce cnt ad adlen len

val encrypt: #k:pos -> alg:cipher_alg k ->
    ciphertext:u8s ->
    tag:u8s{length tag = 16 /\ disjoint ciphertext tag} ->
    key:u8s{length key = k /\ disjoint ciphertext key /\ disjoint tag key} ->
    iv:u8s{length iv = 12 /\ disjoint ciphertext iv /\ disjoint tag iv /\ disjoint key iv} ->
    ad:u8s{disjoint ciphertext ad /\ disjoint tag ad /\ disjoint key ad /\ disjoint iv ad} ->
    adlen:u32{length ad = U32.v adlen} ->
    plaintext:u8s{length plaintext = length ciphertext /\ disjoint ciphertext plaintext /\ disjoint tag plaintext /\ disjoint key plaintext /\ disjoint iv plaintext /\ disjoint ad plaintext} ->
    len:u32{length ciphertext = U32.v len} ->
    STL unit
    (requires (fun h -> live h ciphertext /\ live h tag /\ live h key /\ live h iv /\ live h ad /\ live h plaintext))
    (ensures (fun h0 _ h1 -> live h1 ciphertext /\ live h1 tag /\ live h1 key /\ live h1 iv /\ live h1 ad /\ live h1 plaintext
        /\ modifies_2 ciphertext tag h0 h1))
let encrypt #k alg ciphertext tag key iv ad adlen plaintext len =
  encrypt_body #k alg ciphertext tag key iv 1ul ad adlen plaintext len
*)
