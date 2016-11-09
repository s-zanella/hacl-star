module Hacl.SecretBox

open FStar.Buffer
open FStar.ST
open Hacl.Constants
open Hacl.Policies
open Hacl.Cast

(* Module abbreviations *)
module HS  = FStar.HyperStack
module B   = FStar.Buffer
module U8  = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module H8  = Hacl.UInt8
module H32 = Hacl.UInt32
module H64 = Hacl.UInt64


private val set_zero_bytes:
  b:uint8_p{length b >= 16} ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
let set_zero_bytes b =
  let zero = uint8_to_sint8 0uy in
  b.(0ul)  <- zero; b.(1ul)  <- zero; b.(2ul)  <- zero; b.(3ul)  <- zero;
  b.(4ul)  <- zero; b.(5ul)  <- zero; b.(6ul)  <- zero; b.(7ul)  <- zero;
  b.(8ul)  <- zero; b.(9ul)  <- zero; b.(10ul) <- zero; b.(11ul) <- zero;
  b.(12ul) <- zero; b.(13ul) <- zero; b.(14ul) <- zero; b.(15ul) <- zero;
  b.(16ul) <- zero; b.(17ul) <- zero; b.(18ul) <- zero; b.(19ul) <- zero;
  b.(20ul) <- zero; b.(21ul) <- zero; b.(22ul) <- zero; b.(23ul) <- zero;
  b.(24ul) <- zero; b.(25ul) <- zero; b.(26ul) <- zero; b.(27ul) <- zero;
  b.(28ul) <- zero; b.(29ul) <- zero; b.(30ul) <- zero; b.(31ul) <- zero


val crypto_secretbox_detached:
  c:uint8_p ->
  mac:uint8_p{length mac = crypto_secretbox_MACBYTES} ->
  m:uint8_p ->
  mlen:u64{let len = U64.v mlen in len = length m /\ len = length c}  ->
  n:uint8_p{length n = crypto_secretbox_NONCEBYTES} ->
  k:uint8_p{length k = crypto_secretbox_KEYBYTES} ->
  Stack u32
    (requires (fun h -> live h c /\ live h mac /\ live h m /\ live h n /\ live h k))
    (ensures  (fun h0 z h1 -> modifies_2 c mac h0 h1 /\ live h1 c /\ live h1 mac))
let crypto_secretbox_detached c mac m mlen n k =
  push_frame();
  let hsalsa_state = create (uint8_to_sint8 0uy) 96ul in
  let subkey = sub hsalsa_state  0ul 32ul in
  let block0 = sub hsalsa_state 32ul 64ul in

  let zerobytes = 32ul in
  let zerobytes_64 = Int.Cast.uint32_to_uint64 zerobytes in
  let mlen0 =
      if (U64 (mlen >^ (64uL -^ zerobytes_64))) then U64 (64uL -^ zerobytes_64) else mlen in
  let mlen0_32 = Int.Cast.uint64_to_uint32 mlen0 in
  blit m 0ul block0 zerobytes mlen0_32;
  Hacl.Symmetric.HSalsa20.crypto_core_hsalsa20 subkey (sub n 0ul 16ul) k;
  Hacl.Symmetric.HSalsa20.crypto_stream_salsa20_xor block0
                                                    block0
                                                    (U64 (mlen0 +^ zerobytes_64))
                                                    (sub n 16ul 8ul)
                                                    subkey;
  blit block0 zerobytes c 0ul mlen0_32;
  if (U64 (mlen >^ mlen0)) then
    Hacl.Symmetric.HSalsa20.crypto_stream_salsa20_xor_ic (offset c mlen0_32)
                                                         (offset m mlen0_32)
                                                         (U64 (mlen -^ mlen0))
                                                         (sub n 16ul 8ul)
                                                         1uL
                                                         subkey;
  Hacl.Symmetric.Poly1305_64.crypto_onetimeauth mac c mlen block0;
  pop_frame();
  0ul


val crypto_secretbox_open_detached:
  m:uint8_p ->
  c:uint8_p ->
  mac:uint8_p{length mac = crypto_secretbox_MACBYTES /\ declassifiable mac} ->
  clen:u64{let len = U64.v clen in len = length m /\ len = length c}  ->
  n:uint8_p{length n = crypto_secretbox_NONCEBYTES} ->
  k:uint8_p{length k = crypto_secretbox_KEYBYTES} ->
  Stack u32
    (requires (fun h -> live h m /\ live h c /\ live h mac /\ live h n /\ live h k))
    (ensures  (fun h0 z h1 -> modifies_1 m h0 h1 /\ live h1 m))
let crypto_secretbox_open_detached m c mac clen n k =
  push_frame();
  let hsalsa_state = create (uint8_to_sint8 0uy) 112ul in
  let subkey = sub hsalsa_state 0ul 32ul in
  let block0 = sub hsalsa_state 32ul 64ul in
  let tmp_mac = sub hsalsa_state 96ul 16ul in

  Hacl.Symmetric.HSalsa20.crypto_core_hsalsa20 subkey (sub n 0ul 16ul) k;
  Hacl.Symmetric.HSalsa20.crypto_stream_salsa20 block0 32uL (sub n 16ul 8ul) subkey;

  Hacl.Symmetric.Poly1305_64.crypto_onetimeauth tmp_mac c clen block0;
  assume (Hacl.Policies.declassifiable tmp_mac);
  let verify = cmp_bytes mac tmp_mac 16ul in
  let zerobytes = 32ul in
  let zerobytes_64 = 32uL in
  let clen0 =
    if (U64 (clen >^ (64uL -^ zerobytes_64))) then U64 (64uL -^ zerobytes_64) else clen in
  let clen0_32 = Int.Cast.uint64_to_uint32 clen0 in
  let z =
    if U8 (verify =^ 0uy) then (
      blit c 0ul block0 zerobytes clen0_32;
      Hacl.Symmetric.HSalsa20.crypto_stream_salsa20_xor block0
                                                        block0
                                                        (U64 (zerobytes_64 +^ clen0))
                                                        (sub n 16ul 8ul)
                                                        subkey;
      blit block0 zerobytes m 0ul clen0_32;
      if (U64 (clen >^ clen0))
        then Hacl.Symmetric.HSalsa20.crypto_stream_salsa20_xor_ic (offset m clen0_32)
                                                                  (offset c clen0_32)
                                                                  (U64 (clen -^ clen0))
                                                                  (sub n 16ul 8ul)
                                                                  1uL
                                                                  subkey;
      0x0ul
    )
    else 0xfffffffful in
  pop_frame();
  z


val crypto_secretbox_easy:
  c:uint8_p ->
  m:uint8_p ->
  mlen:u64{let len = U64.v mlen in len <= length m /\ len + crypto_secretbox_MACBYTES <= length c}  ->
  n:uint8_p{length n = crypto_secretbox_NONCEBYTES} ->
  k:uint8_p{length k = crypto_secretbox_KEYBYTES} ->
  Stack u32
    (requires (fun h -> live h c /\ live h m /\ live h n /\ live h k))
    (ensures  (fun h0 z h1 -> modifies_1 c h0 h1 /\ live h1 c))
let crypto_secretbox_easy c m mlen n k =
  let mlen_ = FStar.Int.Cast.uint64_to_uint32 mlen in
  let c'   = sub c 16ul (U32 (mlen_+^16ul)) in
  let mac  = sub c 0ul 16ul in
  crypto_secretbox_detached c' mac m mlen n k


val crypto_secretbox_open_easy:
  m:uint8_p ->
  c:uint8_p ->
  clen:u64{let len = U64.v clen in len = length m + crypto_secretbox_MACBYTES /\ len = length c}  ->
  n:uint8_p{length n = crypto_secretbox_NONCEBYTES} ->
  k:uint8_p{length k = crypto_secretbox_KEYBYTES} ->
  Stack u32
    (requires (fun h -> live h c /\ live h m /\ live h n /\ live h k))
    (ensures  (fun h0 z h1 -> modifies_1 m h0 h1 /\ live h1 m))
let crypto_secretbox_open_easy m c clen n k =
  let clen_ = FStar.Int.Cast.uint64_to_uint32 clen in
  let c'  = sub c 16ul clen_ in
  let mac = sub c 0ul 16ul in
  crypto_secretbox_open_detached m c' mac (U64 (clen -^ 16uL)) n k

open Hacl.Symmetric.Poly1305 // Hacl to make load the module with autodep