## Small dependency-free SHA-256 implementation for the state-DAG prototype.
## The wire format uses lowercase hexadecimal digests.

type
  Sha256Digest* = array[32, byte]

const K: array[64, uint32] = [
  0x428a2f98'u32, 0x71374491'u32, 0xb5c0fbcf'u32, 0xe9b5dba5'u32,
  0x3956c25b'u32, 0x59f111f1'u32, 0x923f82a4'u32, 0xab1c5ed5'u32,
  0xd807aa98'u32, 0x12835b01'u32, 0x243185be'u32, 0x550c7dc3'u32,
  0x72be5d74'u32, 0x80deb1fe'u32, 0x9bdc06a7'u32, 0xc19bf174'u32,
  0xe49b69c1'u32, 0xefbe4786'u32, 0x0fc19dc6'u32, 0x240ca1cc'u32,
  0x2de92c6f'u32, 0x4a7484aa'u32, 0x5cb0a9dc'u32, 0x76f988da'u32,
  0x983e5152'u32, 0xa831c66d'u32, 0xb00327c8'u32, 0xbf597fc7'u32,
  0xc6e00bf3'u32, 0xd5a79147'u32, 0x06ca6351'u32, 0x14292967'u32,
  0x27b70a85'u32, 0x2e1b2138'u32, 0x4d2c6dfc'u32, 0x53380d13'u32,
  0x650a7354'u32, 0x766a0abb'u32, 0x81c2c92e'u32, 0x92722c85'u32,
  0xa2bfe8a1'u32, 0xa81a664b'u32, 0xc24b8b70'u32, 0xc76c51a3'u32,
  0xd192e819'u32, 0xd6990624'u32, 0xf40e3585'u32, 0x106aa070'u32,
  0x19a4c116'u32, 0x1e376c08'u32, 0x2748774c'u32, 0x34b0bcb5'u32,
  0x391c0cb3'u32, 0x4ed8aa4a'u32, 0x5b9cca4f'u32, 0x682e6ff3'u32,
  0x748f82ee'u32, 0x78a5636f'u32, 0x84c87814'u32, 0x8cc70208'u32,
  0x90befffa'u32, 0xa4506ceb'u32, 0xbef9a3f7'u32, 0xc67178f2'u32
]

func rotr(x: uint32, n: int): uint32 =
  (x shr n) or (x shl (32 - n))

proc sha256*(input: string): Sha256Digest =
  var data = newSeq[byte](input.len)
  for i, c in input: data[i] = byte(ord(c))
  let bitLength = uint64(data.len) * 8'u64
  data.add(0x80'u8)
  while data.len mod 64 != 56: data.add(0'u8)
  for i in countdown(7, 0):
    data.add(byte((bitLength shr (i * 8)) and 0xff'u64))

  var h = [0x6a09e667'u32, 0xbb67ae85'u32, 0x3c6ef372'u32,
           0xa54ff53a'u32, 0x510e527f'u32, 0x9b05688c'u32,
           0x1f83d9ab'u32, 0x5be0cd19'u32]
  for offset in countup(0, data.len - 64, 64):
    var w: array[64, uint32]
    for i in 0 ..< 16:
      let j = offset + i * 4
      w[i] = (uint32(data[j]) shl 24) or (uint32(data[j+1]) shl 16) or
             (uint32(data[j+2]) shl 8) or uint32(data[j+3])
    for i in 16 ..< 64:
      let x = w[i - 15]
      let s0 = rotr(x, 7) xor rotr(x, 18) xor (x shr 3)
      let y = w[i - 2]
      let s1 = rotr(y, 17) xor rotr(y, 19) xor (y shr 10)
      w[i] = w[i - 16] + s0 + w[i - 7] + s1
    var a=h[0]; var b=h[1]; var c=h[2]; var d=h[3]
    var e=h[4]; var f=h[5]; var g=h[6]; var hh=h[7]
    for i in 0 ..< 64:
      let s1 = rotr(e, 6) xor rotr(e, 11) xor rotr(e, 25)
      let ch = (e and f) xor ((not e) and g)
      let t1 = hh + s1 + ch + K[i] + w[i]
      let s0 = rotr(a, 2) xor rotr(a, 13) xor rotr(a, 22)
      let maj = (a and b) xor (a and c) xor (b and c)
      let t2 = s0 + maj
      hh=g; g=f; f=e; e=d + t1
      d=c; c=b; b=a; a=t1 + t2
    h[0] = h[0] + a; h[1] = h[1] + b
    h[2] = h[2] + c; h[3] = h[3] + d
    h[4] = h[4] + e; h[5] = h[5] + f
    h[6] = h[6] + g; h[7] = h[7] + hh
  for i in 0 ..< 8:
    for j in 0 ..< 4:
      result[i * 4 + j] = byte((h[i] shr ((3 - j) * 8)) and 0xff'u32)

proc toHex*(digest: Sha256Digest): string =
  const HexChars = "0123456789abcdef"
  result = newStringOfCap(64)
  for b in digest:
    result.add(HexChars[int(b shr 4)])
    result.add(HexChars[int(b and 0x0f)])

proc sha256Hex*(input: string): string = toHex(sha256(input))
