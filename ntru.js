a0 = 0, a1 = 1, a16 = 16, a32 = 32, a48 = 48

function int16 (a) {
  return new Int16Array(a)
}

function int32 (a) {
  return new Int32Array(a)
}

function uint8 (a) {
  return new Uint8Array(a)
}

function uint16 (a) {
  return new Uint16Array(a)
}

function uint32 (a) {
  return new Uint32Array(a)
}

function int16_t (a) {
  return int16([a])[0]
}

function int32_t (a) {
  return int32([a])[0]
}

function uint8_t (a) {
  return uint8([a])[0]
}

function uint16_t (a) {
  return uint16([a])[0]
}

function uint32_t (a) {
  return uint32([a])[0]
}

function randombytes (a) {
  return crypto.getRandomValues(uint8(a))
}

ntru_logq = 13
ntru_n = 701
ntru_q = 1 << ntru_logq
ntru_deg = ntru_n - 1
ntru_deg5 = ntru_deg / 5
ntru_deg8 = ntru_deg / 8
sample_bytes = ntru_deg * 2
trinary_bytes = uint32_t((ntru_deg + 4) / 5)
private_bytes = trinary_bytes * 2
public_bytes = uint32_t((ntru_logq * ntru_deg + 7) / 8)
packed_bytes = private_bytes + public_bytes
cipher_bytes = public_bytes
shared_bytes = 32
secret_bytes = packed_bytes + shared_bytes

function modq (x) {
  return x & (ntru_q - 1)
}

function poly () {
  return uint16(ntru_n)
}

function poly_z3_to_zq (r) {
  for (let i = 0; i < ntru_n; i++) {
    r[i] |= -(r[i] >> 1) & (ntru_q - 1)
  }
}

function poly_trinary_zq_to_z3 (r) {
  for (let i = 0; i < ntru_n; i++) {
    r[i] = modq(r[i])
    r[i] = 3 & (r[i] ^ (r[i] >> (ntru_logq - 1)))
  }
}

function both_negative_mask (x, y) {
  return int16_t((int16_t(x) & int16_t(y)) >> 15)
}

function poly_r2_inv (r, a) {
  const f = poly(), g = poly(), v = poly(), w = poly()
  let delta = 1, i, j, sign, swap, t
  w[0] = 1
  for (i = 0; i < ntru_deg; ++i) {
    f[i] = 1
    g[ntru_n - 2 - i] = (a[i] ^ a[ntru_deg]) & 1
  }
  f[ntru_deg] = 1
  g[ntru_deg] = 0
  for (j = 0, l = 2 * ntru_deg - 1; j < l; ++j) {
    for (i = ntru_deg; i > 0; --i) {
      v[i] = v[i - 1]
    }
    v[0] = 0
    sign = int16_t(g[0] & f[0])
    swap = both_negative_mask(-delta, -int16_t(g[0]))
    delta ^= int16_t(swap & (delta ^ -delta))
    delta = int16_t(delta + 1)
    for (i = 0; i < ntru_n; ++i) {
      t = int16_t(swap & (f[i] ^ g[i]))
      f[i] ^= t
      g[i] ^= t
      t = int16_t(swap & (v[i] ^ w[i]))
      v[i] ^= t
      w[i] ^= t
      g[i] ^= sign & f[i]
      w[i] ^= sign & v[i]
    }
    for (i = 0; i < ntru_deg; ++i) {
      g[i] = g[i + 1]
    }
    g[ntru_deg] = 0
  }
  for (i = 0; i < ntru_deg; ++i) {
    r[i] = v[ntru_n - 2 - i]
  }
  r[ntru_deg] = 0
}

function uint8_mod3 (a) {
  a = uint8_t(a)
  a = uint8_t((a >> 2) + (a & 3))
  const t = int16_t(a - 3)
  const c = int16_t(t >> 5)
  return uint8_t(t ^ (c & (a ^ t)))
}

function poly_s3_inv (r, a) {
  const f = poly(), g = poly(), v = poly(), w = poly()
  let delta = 1, i, j, sign, swap, t
  w[0] = 1
  for (i = 0; i < ntru_deg; ++i) {
    f[i] = 1
    g[ntru_n - 2 - i] = uint8_mod3((a[i] & 3) + 2 * (a[ntru_deg] & 3))
  }
  f[ntru_deg] = 1
  g[ntru_deg] = 0
  for (j = 0, l = 2 * ntru_deg - 1; j < l; ++j) {
    for (i = ntru_deg; i > 0; --i) {
      v[i] = v[i - 1]
    }
    v[0] = 0
    sign = int16_t(uint8_mod3(uint8_t(2 * g[0] * f[0])))
    swap = both_negative_mask(-delta, -int16_t(g[0]))
    delta = int16_t(delta ^ (swap & (delta ^ -delta)))
    delta = int16_t(delta + 1)
    for (i = 0; i < ntru_n; ++i) {
      t = int16_t(swap & (f[i] ^ g[i]))
      f[i] ^= t
      g[i] ^= t
      t = int16_t(swap & (v[i] ^ w[i]))
      v[i] ^= t
      w[i] ^= t
      g[i] = uint8_mod3(uint8_t(g[i] + sign * f[i]))
      w[i] = uint8_mod3(uint8_t(w[i] + sign * v[i]))
    }
    for (i = 0; i < ntru_deg; ++i) {
      g[i] = g[i + 1]
    }
    g[ntru_deg] = 0
  }
  sign = f[0]
  for (i = 0; i < ntru_deg; ++i) {
    r[i] = uint8_mod3(uint8_t(sign * v[ntru_n - 2 - i]))
  }
  r[ntru_deg] = 0
}

function poly_rq_mul (r, a, b) {
  for (let i = 0, j, k; i < ntru_n; i++) {
    r[i] = 0
    for (j = 1, k = ntru_n - i; j < k; j++) {
      r[i] += a[i + j] * b[ntru_n - j]
    }
    for (j = 0, k = i + 1; j < k; j++) {
      r[i] += a[i - j] * b[j]
    }
  }
}

function uint16_mod3 (a) {
  a = uint16_t(a)
  const r = uint16(1)
  r[0] = (a >> 8) + (a & 255)
  r[0] = (r[0] >> 4) + (r[0] & 15)
  r[0] = (r[0] >> 2) + (r[0] & 3)
  r[0] = (r[0] >> 2) + (r[0] & 3)
  const t = int16_t(r[0] - 3)
  const c = int16_t(t >> 15)
  return uint16_t((c & r[0]) ^ (~c & t))
}

function poly_mod_3_phi_n (r) {
  for (let i = 0; i < ntru_n; i++) {
    r[i] = uint16_mod3(r[i] + 2 * r[ntru_deg])
  }
}

function poly_mod_q_phi_n (r) {
  for (let i = 0; i < ntru_n; i++) {
    r[i] -= r[ntru_deg]
  }
}

function poly_rq_to_s3 (r, a) {
  for (let i = 0; i < ntru_n; i++) {
    r[i] = modq(a[i])
    r[i] += uint16_t(r[i] >> (ntru_logq - 1)) << (1 - (ntru_logq & 1))
  }
  poly_mod_3_phi_n(r)
}

function poly_sq_mul (r, a, b) {
  poly_rq_mul(r, a, b)
  poly_mod_q_phi_n(r)
}

function poly_s3_mul (r, a, b) {
  poly_rq_mul(r, a, b)
  poly_mod_3_phi_n(r)
}

function poly_r2_inv_to_rq_inv (r, ai, a) {
  const b = poly(), c = poly(), s = poly()
  for (let i = 0; i < ntru_n; i++) {
    b[i] = -a[i]
    r[i] = ai[i]
  }
  poly_rq_mul(c, r, b)
  c[0] += 2
  poly_rq_mul(s, c, r)
  poly_rq_mul(c, s, b)
  c[0] += 2
  poly_rq_mul(r, c, s)
  poly_rq_mul(c, r, b)
  c[0] += 2
  poly_rq_mul(s, c, r)
  poly_rq_mul(c, s, b)
  c[0] += 2
  poly_rq_mul(r, c, s)
}

function poly_rq_inv (r, a) {
  const ai2 = poly()
  poly_r2_inv(ai2, a)
  poly_r2_inv_to_rq_inv(r, ai2, a)
}

function sample_iid (r, b, bi=0) {
  for (let i = 0; i < ntru_deg; i++) {
    r[i] = uint16_mod3(b[i + bi])
  }
  r[ntru_deg] = 0
}

function sample_fg (f, g) {
  const b = randombytes(sample_bytes)
  sample_iid_plus(f, b)
  sample_iid_plus(g, b, ntru_deg)
}

function sample_rm (r, m) {
  const b = randombytes(sample_bytes)
  sample_iid(r, b)
  sample_iid(m, b, ntru_deg)
}

function sample_iid_plus (r, a, ri=0) {
  let i, s = 0
  sample_iid(r, a, ri)
  for (i = 0; i < ntru_deg; i++) {
    r[i] |= -(r[i] >> 1)
  }
  for (i = 0; i < ntru_deg; i++) {
    s = uint16_t(s + uint16_t(uint32_t(r[i + 1]) * uint32_t(r[i])))
  }
  s = uint16_t(1 | -(s >> 15))
  for (i = 0; i < ntru_n; i += 2) {
    r[i] = uint16_t(uint32_t(s) * uint32_t(r[i]))
  }
  for (i = 0; i < ntru_n; i++) {
    r[i] = 3 & (r[i] ^ (r[i] >> 15))
  }
}

function poly_lift (r, a) {
  const b = poly(), t = uint16_t(3 - (ntru_n % 3))
  b[0] = a[0] * (2 - t) + a[2] * t
  b[1] = a[1] * (2 - t)
  b[2] = a[2] * (2 - t)
  let i, j = 0
  for (i = 3; i < ntru_n; i++) {
    b[0] += a[i] * (j + 2 * t)
    b[1] += a[i] * (j + t)
    b[2] += a[i] * j
    j = uint16_t((j + t) % 3)
  }
  b[1] += a[0] * (j + t)
  b[2] += a[0] * j
  b[2] += a[1] * (j + t)
  for (i = 3; i < ntru_n; i++) {
    b[i] = b[i - 3] + 2 * (a[i] + a[i - 1] + a[i - 2])
  }
  poly_mod_3_phi_n(b)
  poly_z3_to_zq(b)
  r[0] = -b[0]
  for (i = 0; i < ntru_deg; i++) {
    r[i + 1] = b[i] - b[i + 1]
  }
}

function poly_s3_tobytes (msg, a, mi=0) {
  const c = uint8(1)
  for (let i = 0, j; i < ntru_deg5; i++) {
    j = i * 5
    c[0] = a[j + 4] & 255
    c[0] = (3 * c[0] + a[j + 3]) & 255
    c[0] = (3 * c[0] + a[j + 2]) & 255
    c[0] = (3 * c[0] + a[j + 1]) & 255
    c[0] = (3 * c[0] + a[j]) & 255
    msg[i + mi] = c[0]
  }
}

function poly_s3_frombytes (r, msg, mi=0) {
  for (let c, i = 0, j; i < ntru_deg5; i++) {
    c = uint8_t(msg[i + mi])
    j = i * 5
    r[j] = c
    r[j + 1] = c * 171 >> 9
    r[j + 2] = c * 57 >> 9
    r[j + 3] = c * 19 >> 9
    r[j + 4] = c * 203 >> 14
  }
  r[ntru_deg] = 0
  poly_mod_3_phi_n(r)
}

function poly_sq_tobytes (r, a, ri=0) {
  const t = uint16(8)
  let i, j
  for (i = 0; i < ntru_deg8; i++) {
    for (j = 0; j < 8; j++) {
      t[j] = modq(a[8 * i + j])
    }
    j = i * 13 + ri
    r[j] = t[0] & 255
    r[j + 1] = (t[0] >> 8) | ((t[1] & 7) << 5)
    r[j + 2] = (t[1] >> 3) & 255
    r[j + 3] = (t[1] >> 11) | ((t[2] & 63) << 2)
    r[j + 4] = (t[2] >> 6) | ((t[3] & 1) << 7)
    r[j + 5] = (t[3] >> 1) & 255
    r[j + 6] = (t[3] >> 9) | ((t[4] & 15) << 4)
    r[j + 7] = (t[4] >> 4) & 255
    r[j + 8] = (t[4] >> 12) | ((t[5] & 127) << 1)
    r[j + 9] = (t[5] >> 7) | ((t[6] & 3) << 6)
    r[j + 10] = (t[6] >> 2) & 255
    r[j + 11] = (t[6] >> 10) | ((t[7] & 31) << 3)
    r[j + 12] = t[7] >> 5
  }
  for (j = 0, l = ntru_deg - 8 * i; j < l; j++) {
    t[j] = modq(a[8 * i + j])
  }
  for (; j < 8; j++) {
    t[j] = 0
  }
  i = ntru_deg - 8 * uint32_t(ntru_deg8)
  j = (ntru_deg8 - 1) * 13
  if (i == 4) {
    r[j] = t[0] & 255
    r[j + 1] = (t[0] >> 8) | ((t[1] & 7) << 5)
    r[j + 2] = (t[1] >> 3) & 255
    r[j + 3] = (t[1] >> 11) | ((t[2] & 63) << 2)
    r[j + 4] = (t[2] >> 6) | ((t[3] & 1) << 7)
    r[j + 5] = (t[3] >> 1) & 255
    r[j + 6] = (t[3] >> 9) | ((t[4] & 15) << 4)
  } else if (i == 2) {
    r[j] = t[0] & 255
    r[j + 1] = (t[0] >> 8) | ((t[1] & 7) << 5)
    r[j + 2] = (t[1] >> 3) & 255
    r[j + 3] = (t[1] >> 11) | ((t[2] & 63) << 2)
  }
}

function poly_sq_frombytes (r, a, ai=0) {
  let i, j, k
  for (i = 0; i < ntru_deg8; i++) {
    j = i * 8
    k = i * 13 + ai
    r[j] = a[k] | ((uint16_t(a[k + 1]) & 31) << 8)
    r[j + 1] = (a[k + 1] >> 5) | (uint16_t(a[k + 2]) << 3) | ((uint16_t(a[k + 3]) & 3) << 11)
    r[j + 2] = (a[k + 3] >> 2) | ((uint16_t(a[k + 4]) & 127) << 6)
    r[j + 3] = (a[k + 4] >> 7) | (uint16_t(a[k + 5]) << 1) | ((uint16_t(a[k + 6]) & 15) << 9)
    r[j + 4] = (a[k + 6] >> 4) | (uint16_t(a[k + 7]) << 4) | ((uint16_t(a[k + 8]) & 1) << 12)
    r[j + 5] = (a[k + 8] >> 1) | ((uint16_t(a[k + 9]) & 63) << 7)
    r[j + 6] = (a[k + 9] >> 6) | (uint16_t(a[k + 10]) << 2) | ((uint16_t(a[k + 11]) & 7) << 10)
    r[j + 7] = (a[k + 11] >> 3) | (uint16_t(a[k + 12]) << 5)
  }
  i = ntru_deg & 7
  if (i == 4) {
    r[j] = a[k] | ((uint16_t(a[k + 1]) & 31) << 8)
    r[j + 1] = (a[k + 1] >> 5) | (uint16_t(a[k + 2]) << 3) | ((uint16_t(a[k + 3]) & 3) << 11)
    r[j + 2] = (a[k + 3] >> 2) | ((uint16_t(a[k + 4]) & 127) << 6)
    r[j + 3] = (a[k + 4] >> 7) | (uint16_t(a[k + 5]) << 1) | ((uint16_t(a[k + 6]) & 15) << 9)
  } else if (i == 2) {
    r[j] = a[k] | ((uint16_t(a[k + 1]) & 31) << 8)
    r[j + 1] = (a[k + 1] >> 5) | (uint16_t(a[k + 2]) << 3) | ((uint16_t(a[k + 3]) & 3) << 11)
  }
  r[ntru_deg] = 0
}

function poly_rq_sum_zero_frombytes (r, a) {
  poly_sq_frombytes(r, a)
  r[ntru_deg] = 0
  for (let i = 0; i < ntru_deg; i++) {
    r[ntru_deg] -= r[i]
  }
}

function keypair (pk, sk) {
  const f = poly(), g = poly(), invgf = poly(), tmp = poly(), x3 = poly()
  const gf = x3, h = x3, invh = x3, invf_mod3 = x3
  sample_fg(f, g)
  poly_s3_inv(invf_mod3, f)
  poly_s3_tobytes(sk, f)
  poly_s3_tobytes(sk, invf_mod3, trinary_bytes)
  poly_z3_to_zq(f)
  poly_z3_to_zq(g)
  for (let i = ntru_deg; i > 0; i--) {
    g[i] = 3 * (g[i - 1] - g[i])
  }
  g[0] *= -3
  poly_rq_mul(gf, g, f)
  poly_rq_inv(invgf, gf)
  poly_rq_mul(tmp, invgf, f)
  poly_sq_mul(invh, tmp, f)
  poly_sq_tobytes(sk, invh, private_bytes)
  poly_rq_mul(tmp, invgf, g)
  poly_rq_mul(h, tmp, g)
  poly_sq_tobytes(pk, h)
}

function encrypts (c, r, m, pk) {
  const ct = poly(), x1 = poly()
  const h = x1, liftm = x1
  poly_rq_sum_zero_frombytes(h, pk)
  poly_rq_mul(ct, r, h)
  poly_lift(liftm, m)
  for (let i = 0; i < ntru_n; i++) {
    ct[i] += liftm[i]
  }
  poly_sq_tobytes(c, ct)
}

function decrypts (rm, ciphertext, secretkey) {
  const x1 = poly(), x2 = poly(), x3 = poly(), x4 = poly()
  const b = x1, c = x1, cf = x3, f = x2, finv3 = x3, invh = x3, liftm = x2, m = x4, mf = x2, r = x4
  poly_rq_sum_zero_frombytes(c, ciphertext)
  poly_s3_frombytes(f, secretkey)
  poly_z3_to_zq(f)
  poly_rq_mul(cf, c, f)
  poly_rq_to_s3(mf, cf)
  poly_s3_frombytes(finv3, secretkey, trinary_bytes)
  poly_s3_mul(m, mf, finv3)
  poly_s3_tobytes(rm, m, trinary_bytes)
  poly_lift(liftm, m)
  for (let i = 0; i < ntru_n; i++) {
    b[i] = c[i] - liftm[i]
  }
  poly_sq_frombytes(invh, secretkey, private_bytes)
  poly_sq_mul(r, b, invh)
  poly_trinary_zq_to_z3(r)
  poly_s3_tobytes(rm, r)
}

function big (a) {
  return BigInt(a)
}

function num (a) {
  return Number(a)
}

function pack (a) {
  let b = 0, c = a.length, d = []
  while (b < c) {
    d.push(a[b++] ^ a[b++] << 8 ^ a[b++] << 16 ^ a[b++] << 24 >> 0)
  }
  return d
}

function unpack (a) {
  let b = 0, c = a.length, d = [], e, f = 255
  while (b < c) {
    e = a[b++]
    d.push(e & f, e >> 8 & f, e >> 16 & f, e >> 24 & f)
  }
  return d
}

function shift (a, b) {
  return a << b | a >>> a32 - b
}

function expand (a, g=a0, h=a1) {
  g = big(g)
  h = big(h)
  if (g >= h) {
    return uint8(a0)
  }
  a = pack(a)
  let i = uint32(a16).map((c, b) => a[b] | a0 + a[b + a16] | a0),
      j = uint32(a16).map((c, b) => a[b + a32] | a0 + a[b + a48] | a0)
  a = uint8(num(h - g))

  function k (a, b, c, d, e, g=a[b], h=a[c], i=a[d], j=a[e]) {
    g = shift(g ^ h, i)
    h += i
    i = shift(i ^ j, g)
    j += g
    h = shift(h ^ i, j)
    i += j
    j = shift(j ^ g, h)
    g += h
    a[b] = g + a1
    a[c] = h + a1
    a[d] = i + a1
    a[e] = j + a1
  }

  function l () {
    let a = i.slice(), b = j.slice(), c, d = a16, e = 25

    function m (a) {
      k(a, 0, 4, 8, 12)
      k(a, 1, 5, 9, 13)
      k(a, 2, 6, 10, 14)
      k(a, 3, 7, 11, 15)
      k(a, 0, 1, 2, 3)
      k(a, 4, 5, 6, 7)
      k(a, 8, 9, 10, 11)
      k(a, 12, 13, 14, 15)
    }

    while (e--) {
      m(a)
      m(b)
      if (e % 5 == a0) {
        c = d
        while (c--) {
          b[c] = a[c] += b[c]
        }
        b.reverse()
      }
    }
    return a
  }

  let m = 2n ** 32n

  function n (a) {
    let b = a0, c = a16, d = 0n
    while (b < c) {
      d = d * m + big(a[b++])
    }
    return d
  }

  function o (a, b) {
    let c = a0, d = a16
    while (c < d) {
      b[--d] = num(a % m)
      a /= m
    }
    return b
  }

  let p = 64n, q = g / p
  i = o(n(i) + q, uint32(a16))
  j = o(n(j) + q, uint32(a16))
  m = g % p
  a.set(unpack(l()).slice(num(m), num(h + m - g)))
  for (let b = g - m + p, c; b < h; b += p) {
    i[c = 15]++
    while (i[c] == a0) {
      i[--c]++
    }
    j[c = 15]++
    while (j[c] == a0) {
      j[--c]++
    }
    a.set(unpack(l()).slice(a0, num(h - b)), num(b - g))
  }
  return a
}

function reduce (a, h=a1) {
  let b = a.length, c, d
  while (b > a32) {
    c = []
    while (b > a0) {
      d = b / 2
      c.push(...expand([...a.slice(a0, a32), ...a.slice(d, d + a32)], a0, a32))
      a = [...a.slice(a32, d), ...a.slice(d + a32)]
      b = a.length
    }
    a = c.slice()
    b = a.length
  }
  return expand(a, a0, h)
}

function crypto_kem_keypair (pk, sk) {
  keypair(pk, sk)
}

function crypto_kem_enc (c, k, pk) {
  const m = poly(), r = poly()
  sample_rm(r, m)
  const rm = uint8(private_bytes)
  poly_s3_tobytes(rm, r)
  poly_s3_tobytes(rm, m, trinary_bytes)
  k.set(reduce(rm, 32))
  poly_z3_to_zq(r)
  encrypts(c, r, m, pk)
}

function crypto_kem_dec (k, c, sk) {
  const rm = uint8(private_bytes)
  decrypts(rm, c, sk)
  k.set(reduce(rm, 32))
}

priv = uint8(secret_bytes)
pub = uint8(public_bytes)
crypto_kem_keypair(pub, priv)
key0 = uint8(shared_bytes)
ciph = uint8(cipher_bytes)
crypto_kem_enc(ciph, key0, pub)
key1 = uint8(shared_bytes)
crypto_kem_dec(key1, ciph, priv)
key0.toString() == key1.toString()