namespace UInt64

def mapToHex : UInt64 → Char
| 0  => '0' | 1  => '1' | 2  => '2'
| 3  => '3' | 4  => '4' | 5  => '5'
| 6  => '6' | 7  => '7' | 8  => '8'
| 9  => '9' | 10 => 'a' | 11 => 'b'
| 12 => 'c' | 13 => 'd' | 14 => 'e'
| 15 => 'f' | _ => panic! ""

partial def toKBaseNum (x : UInt64) (base : UInt64) (map : UInt64 → Char) : String :=
  if x < base then String.mk [map x]
  else toKBaseNum (x.div base) base map ++ String.mk [map (x.mod base)]

def toHex (x : UInt64) : String := toKBaseNum x 16 mapToHex

def rotate (x : UInt64) (i : UInt64) : UInt64 :=
  if i == 0 then x
  else (x.shiftLeft i).lor (x.shiftRight (64 - i))

def rotateR (x : UInt64) (i : UInt64) : UInt64 := x.rotate ((0 - i).land 63)
def rotateL (x : UInt64) (i : UInt64) : UInt64 := x.rotate i