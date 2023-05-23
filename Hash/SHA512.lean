import Hash.UInt64
-- SHA512 Hashing Algorithm ported from [hashing](https://github.com/wangbj/hashing/blob/master/src/Crypto/Hash/SHA512.hs)

def initHs : Array UInt64 := #[
    0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1
  , 0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179  ]

def initKs : Array UInt64 := #[
    0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc, 0x3956c25bf348b538
  , 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118, 0xd807aa98a3030242, 0x12835b0145706fbe
  , 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2, 0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235
  , 0xc19bf174cf692694, 0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65
  , 0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5, 0x983e5152ee66dfab
  , 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4, 0xc6e00bf33da88fc2, 0xd5a79147930aa725
  , 0x06ca6351e003826f, 0x142929670a0e6e70, 0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed
  , 0x53380d139d95b3df, 0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b
  , 0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30, 0xd192e819d6ef5218
  , 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8, 0x19a4c116b8d2d0c8, 0x1e376c085141ab53
  , 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8, 0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373
  , 0x682e6ff3d6b2b8a3, 0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec
  , 0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b, 0xca273eceea26619c
  , 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178, 0x06f067aa72176fba, 0x0a637dc5a2c898a6
  , 0x113f9804bef90dae, 0x1b710b35131c471b, 0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc
  , 0x431d67c49c100d4c, 0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817  ]

structure Context (a : Type) where
  totalBytesRead : UInt64
  bufferRead : Nat
  buffer : String
  hashValueAcc : a

structure SHA512 where (a b c d e f g h : UInt64)
  deriving BEq

namespace SHA512

def initHash : SHA512 := ⟨a[0]!, a[1]!, a[2]!, a[3]!, a[4]!, a[5]!, a[6]!, a[7]!⟩
where a := initHs

def encodeUInt64 (x : UInt64) : String := 
  let x := x * 8
  let w7 := (x.shiftRight 56).land 0xff
  let w6 := (x.shiftRight 48).land 0xff
  let w5 := (x.shiftRight 40).land 0xff
  let w4 := (x.shiftRight 32).land 0xff
  let w3 := (x.shiftRight 24).land 0xff
  let w2 := (x.shiftRight 16).land 0xff
  let w1 := (x.shiftRight  8).land 0xff
  let w0 := (x.shiftRight  0).land 0xff
  String.mk (List.replicate 8 (Char.ofNat 0) ++ [w7, w6, w5, w4, w3, w2, w1, w0].map (Char.ofNat ∘ UInt64.toNat))

def chunkSize : Nat := 128

def String.splitAt (x : Nat) (s : String) : String × String :=
  let sub := s.toSubstring
  (sub.take x |>.toString, sub.drop x |>.toString)

def lastChunk (msglen : UInt64) (s : String) : Array String :=
  let len := s.length
  let encodedLen := encodeUInt64 msglen
  let helper (bs : String) := 
    let (s1, s2) := String.splitAt chunkSize bs
    #[s1, s2]
  if len < 112 then 
    #[s ++ String.mk (Char.ofNat 0x80 :: List.replicate (111 - len) (Char.ofNat 0x0))
        ++ encodedLen]
  else helper (s ++ String.mk (Char.ofNat 0x80 :: List.replicate (239 - len) (Char.ofNat 0x0))
                 ++ encodedLen)

def mkS0 (x : UInt64) : UInt64 := 
  (x.rotateR 28) |>.xor (x.rotateR 34) |>.xor (x.rotateR 39)
def mkS1 (x : UInt64) : UInt64 := 
  (x.rotateR 14) |>.xor (x.rotateR 18) |>.xor (x.rotateR 41)

def mkS00 (x : UInt64) : UInt64 :=
  (x.rotateR 1) |>.xor (x.rotateR 8) |>.xor (x.shiftRight 7)
def mkS01 (x : UInt64) : UInt64 :=
  (x.rotateR 19) |>.xor (x.rotateR 61) |>.xor (x.shiftRight 6)

def blockUpdate : SHA512 → UInt64 → SHA512
| ⟨a, b, c, d, e, f, g, h⟩, w =>
  let s1 := mkS1 e
  let ch := (e.land f).xor (e.complement.land g)
  let temp1 := h + s1 + ch + w
  let s0 := mkS0 a
  let maj := (a.land b) |>.xor (a.land c) |>.xor (b.land c)
  let temp2 := s0 + maj
  ⟨temp1 + temp2, a, b, c, d + temp1, e, f, g⟩

def readU64 (s : Substring) : UInt64 :=
  s.take 8
    |>.foldl acc 0
  where acc x c := x.shiftLeft 8 + c.toNat.toUInt64

def prepareBlock (s : String) : Array UInt64 := Id.run do
  let mut iou := Array.mkArray 80 0
  let s := s.toSubstring
  iou := iou.set! 0  $ readU64 s
  iou := iou.set! 1  $ readU64 (s.drop 8)
  iou := iou.set! 2  $ readU64 (s.drop 16)
  iou := iou.set! 3  $ readU64 (s.drop 24)
  iou := iou.set! 4  $ readU64 (s.drop 32)
  iou := iou.set! 5  $ readU64 (s.drop 40)
  iou := iou.set! 6  $ readU64 (s.drop 48)
  iou := iou.set! 7  $ readU64 (s.drop 56)
  iou := iou.set! 8  $ readU64 (s.drop 64)
  iou := iou.set! 9  $ readU64 (s.drop 72)
  iou := iou.set! 10 $ readU64 (s.drop 80)
  iou := iou.set! 11 $ readU64 (s.drop 88)
  iou := iou.set! 12 $ readU64 (s.drop 96)
  iou := iou.set! 13 $ readU64 (s.drop 104)
  iou := iou.set! 14 $ readU64 (s.drop 112)
  iou := iou.set! 15 $ readU64 (s.drop 120)
  for i in [16:80] do
    let x1 := iou[i - 16]!
    let x2 := iou[i - 15]!
    let x3 := iou[i -  7]!
    let x4 := iou[i -  2]!
    let s0 := mkS00 x2; let s1 := mkS01 x4
    iou := iou.set! i (x1 + s0 + x3 + s1)
  return iou

def encodeChunk : SHA512 → String → SHA512
| hv@⟨a, b, c, d, e, f, g, h⟩, bs =>
  let ⟨a', b', c', d', e', f', g', h'⟩ := 
    initKs.zipWith (prepareBlock bs) (· + ·)
    |>.foldl blockUpdate hv
  ⟨a+a', b+b', c+c', d+d', e+e', f+f', g+g', h+h'⟩

def init : Context SHA512 := ⟨0, 0, "", initHash⟩

def final : Context SHA512 → SHA512
| ⟨n, _, w, hv⟩ => (lastChunk n w).foldl encodeChunk hv

partial def update : Context SHA512 → String → Context SHA512
| ctx@⟨n, k, w, hv⟩, s =>
  let sizeToRead := chunkSize - k
  let (s1, s') := String.splitAt sizeToRead s
  let sizeRead := s1.length
  if s.isEmpty then ctx
  else if sizeRead < sizeToRead then ⟨n + sizeRead.toUInt64, k + sizeRead, w ++ s1, hv⟩
  else update ⟨n + sizeToRead.toUInt64, 0, "", encodeChunk hv (w ++ s1)⟩ s'

def hash (s : String) : SHA512 :=
  update init s
  |> final

def toArray : SHA512 → Array UInt64
| ⟨a, b, c, d, e, f, g, h⟩ => Array.mkArray8 a b c d e f g h

end SHA512

instance : ToString SHA512 where
  toString x := x.toArray.map (·.toHex) |>.foldl (· ++ ·) ""