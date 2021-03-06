module Hash.Sha512

open FStar.Heap
open SBytes
open SBuffer
open SInt.UInt8
open SInt.UInt64
open SInt.UInt32

#set-options "--lax"


(* [FIPS 180-4] section 4.1.3 *)
val _Ch: x:uint64 -> y:uint64 -> z:uint64 -> Tot uint64
let _Ch x y z = logxor (logand x y) (logand (lognot x) z)

val _Maj: x:uint64 -> y:uint64 -> z:uint64 -> Tot uint64
let _Maj x y z = logxor (logand x y) (logxor (logand x z) (logand y z))

val _Sigma0: x:uint64 -> Tot uint64
let _Sigma0 x = logxor (rotate_right x 28) (logxor (rotate_right x 34) (rotate_right x 39))

val _Sigma1: x:uint64 -> Tot uint64
let _Sigma1 x = logxor (rotate_right x 14) (logxor (rotate_right x 18) (rotate_right x 41))

val _sigma0: x:uint64 -> Tot uint64
let _sigma0 x = logxor (rotate_right x 1) (logxor (rotate_right x 8) (shift_right x 7))

val _sigma1: x:uint64 -> Tot uint64
let _sigma1 x = logxor (rotate_right x 19) (logxor (rotate_right x 61) (shift_right x 6))


(* [FIPS 180-4] section 4.2.3 *)
val k_init: unit -> St (buffer 64)
let k_init () =
  let k = SBuffer.create #64 SInt.UInt64.zero 80  in
  SBuffer.upd k 0 (SInt.UInt64.of_string "0x428a2f98d728ae22");
  SBuffer.upd k 1  (SInt.UInt64.of_string "0x7137449123ef65cd");
  SBuffer.upd k 2  (SInt.UInt64.of_string "0xb5c0fbcfec4d3b2f");
  SBuffer.upd k 3  (SInt.UInt64.of_string "0xe9b5dba58189dbbc");
  SBuffer.upd k 4  (SInt.UInt64.of_string "0x3956c25bf348b538");
  SBuffer.upd k 5  (SInt.UInt64.of_string "0x59f111f1b605d019");
  SBuffer.upd k 6  (SInt.UInt64.of_string "0x923f82a4af194f9b");
  SBuffer.upd k 7  (SInt.UInt64.of_string "0xab1c5ed5da6d8118");
  SBuffer.upd k 8  (SInt.UInt64.of_string "0xd807aa98a3030242");
  SBuffer.upd k 9  (SInt.UInt64.of_string "0x12835b0145706fbe");
  SBuffer.upd k 10 (SInt.UInt64.of_string "0x243185be4ee4b28c");
  SBuffer.upd k 11 (SInt.UInt64.of_string "0x550c7dc3d5ffb4e2");
  SBuffer.upd k 12 (SInt.UInt64.of_string "0x72be5d74f27b896f");
  SBuffer.upd k 13 (SInt.UInt64.of_string "0x80deb1fe3b1696b1");
  SBuffer.upd k 14 (SInt.UInt64.of_string "0x9bdc06a725c71235");
  SBuffer.upd k 15 (SInt.UInt64.of_string "0xc19bf174cf692694");
  SBuffer.upd k 16 (SInt.UInt64.of_string "0xe49b69c19ef14ad2");
  SBuffer.upd k 17 (SInt.UInt64.of_string "0xefbe4786384f25e3");
  SBuffer.upd k 18 (SInt.UInt64.of_string "0x0fc19dc68b8cd5b5");
  SBuffer.upd k 19 (SInt.UInt64.of_string "0x240ca1cc77ac9c65");
  SBuffer.upd k 20 (SInt.UInt64.of_string "0x2de92c6f592b0275");
  SBuffer.upd k 21 (SInt.UInt64.of_string "0x4a7484aa6ea6e483");
  SBuffer.upd k 22 (SInt.UInt64.of_string "0x5cb0a9dcbd41fbd4");
  SBuffer.upd k 23 (SInt.UInt64.of_string "0x76f988da831153b5");
  SBuffer.upd k 24 (SInt.UInt64.of_string "0x983e5152ee66dfab");
  SBuffer.upd k 25 (SInt.UInt64.of_string "0xa831c66d2db43210");
  SBuffer.upd k 26 (SInt.UInt64.of_string "0xb00327c898fb213f");
  SBuffer.upd k 27 (SInt.UInt64.of_string "0xbf597fc7beef0ee4");
  SBuffer.upd k 28 (SInt.UInt64.of_string "0xc6e00bf33da88fc2");
  SBuffer.upd k 29 (SInt.UInt64.of_string "0xd5a79147930aa725");
  SBuffer.upd k 30 (SInt.UInt64.of_string "0x06ca6351e003826f");
  SBuffer.upd k 31 (SInt.UInt64.of_string "0x142929670a0e6e70");
  SBuffer.upd k 32 (SInt.UInt64.of_string "0x27b70a8546d22ffc");
  SBuffer.upd k 33 (SInt.UInt64.of_string "0x2e1b21385c26c926");
  SBuffer.upd k 34 (SInt.UInt64.of_string "0x4d2c6dfc5ac42aed");
  SBuffer.upd k 35 (SInt.UInt64.of_string "0x53380d139d95b3df");
  SBuffer.upd k 36 (SInt.UInt64.of_string "0x650a73548baf63de");
  SBuffer.upd k 37 (SInt.UInt64.of_string "0x766a0abb3c77b2a8");
  SBuffer.upd k 38 (SInt.UInt64.of_string "0x81c2c92e47edaee6");
  SBuffer.upd k 39 (SInt.UInt64.of_string "0x92722c851482353b");
  SBuffer.upd k 40 (SInt.UInt64.of_string "0xa2bfe8a14cf10364");
  SBuffer.upd k 41 (SInt.UInt64.of_string "0xa81a664bbc423001");
  SBuffer.upd k 42 (SInt.UInt64.of_string "0xc24b8b70d0f89791");
  SBuffer.upd k 43 (SInt.UInt64.of_string "0xc76c51a30654be30");
  SBuffer.upd k 44 (SInt.UInt64.of_string "0xd192e819d6ef5218");
  SBuffer.upd k 45 (SInt.UInt64.of_string "0xd69906245565a910");
  SBuffer.upd k 46 (SInt.UInt64.of_string "0xf40e35855771202a");
  SBuffer.upd k 47 (SInt.UInt64.of_string "0x106aa07032bbd1b8");
  SBuffer.upd k 48 (SInt.UInt64.of_string "0x19a4c116b8d2d0c8");
  SBuffer.upd k 49 (SInt.UInt64.of_string "0x1e376c085141ab53");
  SBuffer.upd k 50 (SInt.UInt64.of_string "0x2748774cdf8eeb99");
  SBuffer.upd k 51 (SInt.UInt64.of_string "0x34b0bcb5e19b48a8");
  SBuffer.upd k 52 (SInt.UInt64.of_string "0x391c0cb3c5c95a63");
  SBuffer.upd k 53 (SInt.UInt64.of_string "0x4ed8aa4ae3418acb");
  SBuffer.upd k 54 (SInt.UInt64.of_string "0x5b9cca4f7763e373");
  SBuffer.upd k 55 (SInt.UInt64.of_string "0x682e6ff3d6b2b8a3");
  SBuffer.upd k 56 (SInt.UInt64.of_string "0x748f82ee5defb2fc");
  SBuffer.upd k 57 (SInt.UInt64.of_string "0x78a5636f43172f60");
  SBuffer.upd k 58 (SInt.UInt64.of_string "0x84c87814a1f0ab72");
  SBuffer.upd k 59 (SInt.UInt64.of_string "0x8cc702081a6439ec");
  SBuffer.upd k 60 (SInt.UInt64.of_string "0x90befffa23631e28");
  SBuffer.upd k 61 (SInt.UInt64.of_string "0xa4506cebde82bde9");
  SBuffer.upd k 62 (SInt.UInt64.of_string "0xbef9a3f7b2c67915");
  SBuffer.upd k 63 (SInt.UInt64.of_string "0xc67178f2e372532b");
  SBuffer.upd k 64 (SInt.UInt64.of_string "0xca273eceea26619c");
  SBuffer.upd k 65 (SInt.UInt64.of_string "0xd186b8c721c0c207");
  SBuffer.upd k 66 (SInt.UInt64.of_string "0xeada7dd6cde0eb1e");
  SBuffer.upd k 67 (SInt.UInt64.of_string "0xf57d4f7fee6ed178");
  SBuffer.upd k 68 (SInt.UInt64.of_string "0x06f067aa72176fba");
  SBuffer.upd k 69 (SInt.UInt64.of_string "0x0a637dc5a2c898a6");
  SBuffer.upd k 70 (SInt.UInt64.of_string "0x113f9804bef90dae");
  SBuffer.upd k 71 (SInt.UInt64.of_string "0x1b710b35131c471b");
  SBuffer.upd k 72 (SInt.UInt64.of_string "0x28db77f523047d84");
  SBuffer.upd k 75 (SInt.UInt64.of_string "0x32caab7b40c72493");
  SBuffer.upd k 74 (SInt.UInt64.of_string "0x3c9ebe0a15c9bebc");
  SBuffer.upd k 75 (SInt.UInt64.of_string "0x431d67c49c100d4c");
  SBuffer.upd k 76 (SInt.UInt64.of_string "0x4cc5d4becb3e42b6");
  SBuffer.upd k 77 (SInt.UInt64.of_string "0x597f299cfc657e2a");
  SBuffer.upd k 78 (SInt.UInt64.of_string "0x5fcb6fab3ad6faec");
  SBuffer.upd k 79 (SInt.UInt64.of_string "0x6c44198c4a475817");
  k


(* [FIPS 180-4] section 5.1.2 *)
(* l + 1 + k ≡ 896 mod 1024 *)

(* Compute the number of 1024 bit blocks to store data (112 bytes) and padding (16 bytes) *)
val nblocks: nat -> Tot (n:nat{n >= 1})
let nblocks x = ((x + 16) - ((x + 16) % 128))/128 + 1


(* Compute the pad length *)
val pad_length: nat -> Tot (n:nat{n <= 128})
let pad_length rlen =
  if (rlen % 128) < 112 then 112 - (rlen % 128)
  else 128 + 112 - (rlen % 128)


(* Pad the data and return a buffer of bytes *)
val pad: (pdata :buffer 8 ) ->
         (rdata :buffer 8 ) ->
         (rlen  :nat { length rdata = rlen })
         -> ST unit
              (requires (fun h -> live h rdata))
              (ensures  (fun h0 r h1 -> live h1 rdata))
// TODO: Refinement on the value of the pad -> length raw + rplen = 128
let pad pdata rdata rlen =
  // Value of the raw data length in bits represented as UInt128
  let rlen_128 =
    let v = create #8 SInt.UInt8.zero 16 in
    let v128 = SInt.UInt128.of_int (Prims.op_Multiply rlen 8) in
    SBytes.be_sbytes_of_uint128 v v128;
    v
  in
  // Compute the padding length
  let rplen = pad_length rlen in
  // Generate the padding
  let rpad = create #8 SInt.UInt8.zero rplen in
  SBuffer.upd rpad 0 (SInt.UInt8.of_string "0x80");
  blit rdata 0 pdata 0 rlen;
  blit rpad 0 pdata rlen rplen;
  blit rlen_128 0 pdata (rlen + rplen) 16


(* Store function to handle pdata as a sequence of words *)
val store : (wdata :buffer 64) ->
            (pdata :buffer 8 { length pdata = (Prims.op_Multiply 8 (length wdata)) /\ disjoint wdata pdata }) ->
            (plen  :nat        { length pdata = plen /\ plen = (Prims.op_Multiply 8 (length wdata)) })
            -> ST unit
                 (requires (fun h -> live h wdata /\ live h pdata))
                 (ensures  (fun h0 r h1 -> live h1 wdata /\ live h1 pdata))

let store wdata pdata plen = be_uint64s_of_sbytes wdata pdata plen


(* [FIPS 180-4] section 6.4.2 *)
(* Step 1 : Scheduling function for eighty 64 bit words *)
val wsched_define: (ws     :buffer 64 { length ws = 80 }) ->
                   (wblock :buffer 64 { length wblock = 16 /\ disjoint ws wblock }) ->
                   (t      :ref nat)
                   -> ST unit
                        (requires (fun h -> live h ws /\ live h wblock))
                        (ensures  (fun h0 r h1 -> live h1 ws /\ live h1 wblock))

let rec wsched_define ws wblock t =
  if !t < 16 then begin
    SBuffer.upd ws !t (index wblock !t);
    t := !t + 1;
    wsched_define ws wblock t end
  else if !t < 80 then begin
    let _t16 = index ws (!t-16) in
    let _t15 = index ws (!t-15) in
    let _t7 = index ws (!t-7) in
    let _t2 = index ws (!t-2) in

    let v0 = _sigma1 _t2 in
    let v1 = _sigma0 _t15 in

    let v = (SInt.UInt64.add v0
                              (SInt.UInt64.add _t7
                                                (SInt.UInt64.add v1 _t16)))
    in SBuffer.upd ws !t v;
    t := !t + 1;
    wsched_define ws wblock t end
  else ()


(* [FIPS 180-4] section 5.3.3 *)
(* Define the initial hash value *)
val init : (whash :buffer 64 { length whash = 8 })
           -> ST unit
                (requires (fun h -> live h whash))
                (ensures  (fun h0 r h1 -> live h1 whash))

let init whash =
  SBuffer.upd whash 0 (SInt.UInt64.of_string "0x6a09e667f3bcc908");
  SBuffer.upd whash 1 (SInt.UInt64.of_string "0xbb67ae8584caa73b");
  SBuffer.upd whash 2 (SInt.UInt64.of_string "0x3c6ef372fe94f82b");
  SBuffer.upd whash 3 (SInt.UInt64.of_string "0xa54ff53a5f1d36f1");
  SBuffer.upd whash 4 (SInt.UInt64.of_string "0x510e527fade682d1");
  SBuffer.upd whash 5 (SInt.UInt64.of_string "0x9b05688c2b3e6c1f");
  SBuffer.upd whash 6 (SInt.UInt64.of_string "0x1f83d9abfb41bd6b");
  SBuffer.upd whash 7 (SInt.UInt64.of_string "0x5be0cd19137e2179")


(* Step 3 : Perform logical operations on the working variables *)
val update_inner_loop : (ws    :buffer 64 { length ws = 80 }) ->
                        (whash :buffer 64 { length whash = 8 }) ->
                        (t     :ref int) ->
                        (t1    :buffer 64 { length t1 = 1 }) ->
                        (t2    :buffer 64 { length t2 = 1 }) ->
                        (k     :buffer 64 { length k = 80 /\ disjoint k ws })
                        -> ST unit
                             (requires (fun h -> live h ws /\ live h k))
                             (ensures  (fun h0 r h1 -> live h1 ws /\ live h1 k))

let rec update_inner_loop ws whash t t1 t2 k =
  if !t < 80 then begin
    let _h = index whash 7 in
    let _kt = index k !t in
    let _wt = index ws !t in
    let v0 = _Sigma1 (index whash 4) in
    let v1 = _Ch (index whash 4) (index whash 5) (index whash 6) in
    let _t1 = SInt.UInt64.add _h
                               (SInt.UInt64.add v0
                                                 (SInt.UInt64.add v1
                                                                   (SInt.UInt64.add _kt _wt))) in
    SBuffer.upd t1 0 _t1;
    let z0 = _Sigma0 (index whash 0) in
    let z1 = _Maj (index whash 0) (index whash 1) (index whash 2) in

    let _t2 = SInt.UInt64.add z0 z1 in
    SBuffer.upd t2 0 _t2;

    let _d = (index whash 3) in
    SBuffer.upd whash 7 (index whash 6);
    SBuffer.upd whash 6 (index whash 5);
    SBuffer.upd whash 5 (index whash 4);
    SBuffer.upd whash 4 (SInt.UInt64.add _d _t1);
    SBuffer.upd whash 3 (index whash 2);
    SBuffer.upd whash 2 (index whash 1);
    SBuffer.upd whash 1 (index whash 0);
    SBuffer.upd whash 0 (SInt.UInt64.add _t1 _t2);
    t := !t + 1;
    update_inner_loop ws whash t t1 t2 k end
  else ()


val update_step : (whash :buffer 64 { length whash = 8 }) ->
                  (wdata :buffer 64 { disjoint whash wdata }) ->
                  (ws    :buffer 64 { length ws = 80 /\ disjoint ws whash /\ disjoint ws wdata }) ->
                  (rounds :nat) ->
                  (i     :ref int) ->
                  (t1    :buffer 64 { length t1 = 1 }) ->
                  (t2    :buffer 64 { length t2 = 1 }) ->
                  (k     :buffer 64 { length k = 80 /\ disjoint k whash /\ disjoint k wdata /\ disjoint k ws })
                  -> ST unit
                       (requires (fun h -> live h whash
                                      /\ live h wdata
                                      /\ live h ws
                                      /\ live h k))
                       (ensures  (fun h0 r h1 -> live h1 whash
                                            /\ live h1 wdata
                                            /\ live h1 ws
                                            /\ live h1 k))

let rec update_step ihash wdata ws rounds i t1 t2 k =
  if !i < rounds then begin
    let pos = Prims.op_Multiply !i 16 in
    let wblock = SBuffer.sub wdata pos 16 in

    (* Step 1 : Scheduling function for sixty-four 32 bit words *)
    let ia = ST.alloc 0 in
    wsched_define ws wblock ia;

    (* Step 2 : Initialize the eight working variables *)
    let whash = create #64 SInt.UInt64.zero 8 in
    SBuffer.upd whash 0 (index ihash 0);
    SBuffer.upd whash 1 (index ihash 1);
    SBuffer.upd whash 2 (index ihash 2);
    SBuffer.upd whash 3 (index ihash 3);
    SBuffer.upd whash 4 (index ihash 4);
    SBuffer.upd whash 5 (index ihash 5);
    SBuffer.upd whash 6 (index ihash 6);
    SBuffer.upd whash 7 (index ihash 7);

    (* Step 3 : Perform logical operations on the working variables *)
    let ib = ST.alloc 0 in
    update_inner_loop ws whash ib t1 t2 k;

    (* Step 4 : Compute the ith intermediate hash value *)
    let x01 = index whash 0 in
    let x02 = index ihash 0 in
    let x11 = index whash 1 in
    let x12 = index ihash 1 in
    let x21 = index whash 2 in
    let x22 = index ihash 2 in
    let x31 = index whash 3 in
    let x32 = index ihash 3 in
    let x41 = index whash 4 in
    let x42 = index ihash 4 in
    let x51 = index whash 5 in
    let x52 = index ihash 5 in
    let x61 = index whash 6 in
    let x62 = index ihash 6 in
    let x71 = index whash 7 in
    let x72 = index ihash 7 in
    SBuffer.upd ihash 0 (SInt.UInt64.add x01 x02);
    SBuffer.upd ihash 1 (SInt.UInt64.add x11 x12);
    SBuffer.upd ihash 2 (SInt.UInt64.add x21 x22);
    SBuffer.upd ihash 3 (SInt.UInt64.add x31 x32);
    SBuffer.upd ihash 4 (SInt.UInt64.add x41 x42);
    SBuffer.upd ihash 5 (SInt.UInt64.add x51 x52);
    SBuffer.upd ihash 6 (SInt.UInt64.add x61 x62);
    SBuffer.upd ihash 7 (SInt.UInt64.add x71 x72);
    i := !i + 1;
    update_step ihash wdata ws rounds i t1 t2 k end
  else ()


(* [FIPS 180-4] section 6.4.2 *)
(* Update running hash function *)
val update : (whash  :buffer 64 { length whash = 8 }) ->
             (wdata  :buffer 64 { disjoint whash wdata }) ->
             (rounds :nat )
             -> ST unit
                  (requires (fun h -> live h whash /\ live h wdata))
                  (ensures  (fun h0 r h1 -> live h1 whash /\ live h1 wdata))

let update whash wdata rounds =
  (* Define working variables *)
  let i = ST.alloc 0 in
  let t1 = create #64 SInt.UInt64.zero 1 in
  let t2 = create #64 SInt.UInt64.zero 1 in
  (* Scheduling function *)
  let ws = create #64 SInt.UInt64.zero 80 in
  (* Initialize constant *)
  let k = k_init () in
  (* Perform function *)
  update_step whash wdata ws rounds i t1 t2 k


(* Compute the final value of the hash from the last hash value *)
val finish: (hash  :sbytes    { length hash = 64 }) ->
            (whash :buffer 64 { disjoint whash hash })
            -> ST unit
                 (requires (fun h -> live h hash /\ live h whash))
                 (ensures  (fun h0 r h1 -> live h1 hash /\ live h1 whash))

let finish hash whash = be_sbytes_of_uint64s hash whash 8


(* Compute the sha512 hash of some bytes *)
val sha512: (hash:sbytes { length hash = 64 }) ->
            (data:sbytes { disjoint hash data }) ->
            (len:nat       { length data = len })
            -> ST unit
                 (requires (fun h -> live h hash /\ live h data))
                 (ensures  (fun h0 r h1 -> live h1 data /\ live h1 hash))

let sha512 hash data len =
  let whash = create #64 SInt.UInt64.zero 8 in
  let plen = len + (pad_length len) + 16 in
  let rounds = nblocks plen - 1 in
  let pdata = create #8 SInt.UInt8.zero plen in
  let wlen = plen/8 in
  let wdata = create #64 SInt.UInt64.zero wlen in

  init whash;
  pad pdata data len;
  store wdata pdata plen;
  update whash wdata rounds;
  finish hash whash
