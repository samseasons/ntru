a0 = 0, a1 = 1, a16 = 16, a32 = 32, a48 = 48, a64 = 64, a128 = 128

function big (a) {
  return BigInt(a)
}

function num (a) {
  return Number(a)
}

function int16 (a) {
  return new Int16Array(a)
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

function uint8_t (a) {
  return uint8([a])[0]
}

function uint16_t (a) {
  return uint16([a])[0]
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
trinary_bytes = uint16_t((ntru_deg + 4) / 5)
private_bytes = trinary_bytes * 2
public_bytes = uint16_t((ntru_logq * ntru_deg + 7) / 8)
cipher_bytes = public_bytes
shared_bytes = 32
secret_bytes = private_bytes + public_bytes + shared_bytes

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
  let d = 1, h, i, j, k, t, u = ntru_n - 2
  w[0] = 1
  for (i = 0; i < ntru_deg; ++i) {
    f[i] = 1
    g[u - i] = (a[i] ^ a[ntru_deg]) & 1
  }
  f[ntru_deg] = 1
  g[ntru_deg] = 0
  for (j = 0, l = 2 * ntru_deg - 1; j < l; ++j) {
    for (i = ntru_deg; i > 0; --i) {
      v[i] = v[i - 1]
    }
    v[0] = 0
    h = int16_t(g[0] & f[0])
    k = both_negative_mask(-d, -int16_t(g[0]))
    d = int16_t(d ^ (k & (d ^ -d)))
    d = int16_t(d + 1)
    for (i = 0; i < ntru_n; ++i) {
      t = int16_t(k & (f[i] ^ g[i]))
      f[i] ^= t
      g[i] ^= t
      t = int16_t(k & (v[i] ^ w[i]))
      v[i] ^= t
      w[i] ^= t
      g[i] ^= h & f[i]
      w[i] ^= h & v[i]
    }
    for (i = 0; i < ntru_deg; ++i) {
      g[i] = g[i + 1]
    }
    g[ntru_deg] = 0
  }
  for (i = 0; i < ntru_deg; ++i) {
    r[i] = v[u - i]
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
  let d = 1, h, i, j, k, t, u = ntru_n - 2
  w[0] = 1
  for (i = 0; i < ntru_deg; ++i) {
    f[i] = 1
    g[u - i] = uint8_mod3((a[i] & 3) + 2 * (a[ntru_deg] & 3))
  }
  f[ntru_deg] = 1
  g[ntru_deg] = 0
  for (j = 0, l = 2 * ntru_deg - 1; j < l; ++j) {
    for (i = ntru_deg; i > 0; --i) {
      v[i] = v[i - 1]
    }
    v[0] = 0
    h = int16_t(uint8_mod3(2 * g[0] * f[0]))
    k = both_negative_mask(-d, -int16_t(g[0]))
    d = int16_t(d ^ (k & (d ^ -d)))
    d = int16_t(d + 1)
    for (i = 0; i < ntru_n; ++i) {
      t = int16_t(k & (f[i] ^ g[i]))
      f[i] ^= t
      g[i] ^= t
      t = int16_t(k & (v[i] ^ w[i]))
      v[i] ^= t
      w[i] ^= t
      g[i] = uint8_mod3(g[i] + h * f[i])
      w[i] = uint8_mod3(w[i] + h * v[i])
    }
    for (i = 0; i < ntru_deg; ++i) {
      g[i] = g[i + 1]
    }
    g[ntru_deg] = 0
  }
  h = f[0]
  for (i = 0; i < ntru_deg; ++i) {
    r[i] = uint8_mod3(h * v[u - i])
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
  const b = r[ntru_deg]
  for (let i = 0; i < ntru_n; i++) {
    r[i] -= b
  }
}

function poly_rq_to_s3 (r, a) {
  for (let i = 0; i < ntru_n; i++) {
    r[i] = modq(a[i])
    r[i] += (r[i] >> (ntru_logq - 1)) << (1 - (ntru_logq & 1))
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

function poly_r2_inv_to_rq_inv (r, j, a) {
  const b = poly(), c = poly(), s = poly()
  for (let i = 0; i < ntru_n; i++) {
    b[i] = -a[i]
    r[i] = j[i]
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
  const b = poly()
  poly_r2_inv(b, a)
  poly_r2_inv_to_rq_inv(r, b, a)
}

function sample_iid (r, b, bi=0) {
  for (let i = 0; i < ntru_deg; i++) {
    r[i] = uint16_mod3(b[i + bi])
  }
  r[ntru_deg] = 0
}

function sample_iid_plus (r, a, ri=0) {
  sample_iid(r, a, ri)
  let i, s = uint16(0)
  for (i = 0; i < ntru_deg; i++) {
    r[i] |= -(r[i] >> 1)
  }
  for (i = 0; i < ntru_deg; i++) {
    s[0] += r[i + 1] * r[i]
  }
  s[0] = 1 | -(s[0] >> 15)
  for (i = 0; i < ntru_n; i += 2) {
    r[i] *= s[0]
  }
  for (i = 0; i < ntru_n; i++) {
    r[i] = 3 & (r[i] ^ (r[i] >> 15))
  }
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

function poly_lift (r, a) {
  const b = poly()
  b[0] = a[0] + a[2]
  b[1] = a[1]
  b[2] = a[2]
  let i, j = 0, k
  for (i = 3; i < ntru_n; i++) {
    k = a[i]
    b[0] += k * (j + 2)
    b[1] += k * (j + 1)
    b[2] += k * j
    j = (j + 1) % 3
  }
  k = j + 1
  b[1] += a[0] * k
  b[2] += a[0] * j
  b[2] += a[1] * k
  for (i = 3; i < ntru_n; i++) {
    b[i] = b[i - 3] + 2 * (a[i] + a[i - 1] + a[i - 2])
  }
  poly_mod_3_phi_n(b)
  poly_z3_to_zq(b)
  r[0] = -b[0]
  for (i = 0; i < ntru_deg; i++) {
    j = i + 1
    r[j] = b[i] - b[j]
  }
}

function poly_s3_tobytes (m, a, mi=0) {
  for (let b, i = 0, j; i < ntru_deg5; i++) {
    j = i * 5
    b = a[j + 4] & 255
    b = (3 * b + a[j + 3]) & 255
    b = (3 * b + a[j + 2]) & 255
    b = (3 * b + a[j + 1]) & 255
    m[i + mi] = (3 * b + a[j]) & 255
  }
}

function poly_s3_frombytes (r, m, mi=0) {
  for (let c, i = 0, j; i < ntru_deg5; i++) {
    c = m[i + mi]
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
  for (j = ntru_deg - 8 * i; j < 8; j++) {
    t[j] = 0
  }
  i = ntru_deg - 8 * uint16_t(ntru_deg8)
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

function poly_sq_frombytes (r, a, k=0) {
  let i, j
  for (i = 0; i < ntru_deg8; i++) {
    j = i * 8
    r[j] = a[k++] | ((uint16_t(a[k]) & 31) << 8)
    r[j + 1] = (a[k++] >> 5) | (uint16_t(a[k++]) << 3) | ((uint16_t(a[k]) & 3) << 11)
    r[j + 2] = (a[k++] >> 2) | ((uint16_t(a[k]) & 127) << 6)
    r[j + 3] = (a[k++] >> 7) | (uint16_t(a[k++]) << 1) | ((uint16_t(a[k]) & 15) << 9)
    r[j + 4] = (a[k++] >> 4) | (uint16_t(a[k++]) << 4) | ((uint16_t(a[k]) & 1) << 12)
    r[j + 5] = (a[k++] >> 1) | ((uint16_t(a[k]) & 63) << 7)
    r[j + 6] = (a[k++] >> 6) | (uint16_t(a[k++]) << 2) | ((uint16_t(a[k]) & 7) << 10)
    r[j + 7] = (a[k++] >> 3) | (uint16_t(a[k++]) << 5)
  }
  k -= 13
  i = ntru_deg & 7
  if (i == 4) {
    r[j] = a[k++] | ((uint16_t(a[k]) & 31) << 8)
    r[j + 1] = (a[k++] >> 5) | (uint16_t(a[k++]) << 3) | ((uint16_t(a[k]) & 3) << 11)
    r[j + 2] = (a[k++] >> 2) | ((uint16_t(a[k]) & 127) << 6)
    r[j + 3] = (a[k++] >> 7) | (uint16_t(a[k++]) << 1) | ((uint16_t(a[k]) & 15) << 9)
  } else if (i == 2) {
    r[j] = a[k++] | ((uint16_t(a[k]) & 31) << 8)
    r[j + 1] = (a[k++] >> 5) | (uint16_t(a[k++]) << 3) | ((uint16_t(a[k]) & 3) << 11)
  }
  r[ntru_deg] = 0
}

function poly_rq_sum_zero_frombytes (r, a) {
  poly_sq_frombytes(r, a)
  for (let i = 0; i < ntru_deg; i++) {
    r[ntru_deg] -= r[i]
  }
}

function keypair (p, s) {
  const f = poly(), g = poly(), i = poly(), t = poly(), x = poly()
  const gf = x, h = x, j = x, k = x
  sample_fg(f, g)
  poly_s3_inv(k, f)
  poly_s3_tobytes(s, f)
  poly_s3_tobytes(s, k, trinary_bytes)
  poly_z3_to_zq(f)
  poly_z3_to_zq(g)
  for (let i = ntru_deg; i > 0; i--) {
    g[i] = 3 * (g[i - 1] - g[i])
  }
  g[0] *= -3
  poly_rq_mul(gf, g, f)
  poly_rq_inv(i, gf)
  poly_rq_mul(t, i, f)
  poly_sq_mul(j, t, f)
  poly_sq_tobytes(s, j, private_bytes)
  poly_rq_mul(t, i, g)
  poly_rq_mul(h, t, g)
  poly_sq_tobytes(p, h)
}

function encrypts (c, r, y, p) {
  const t = poly(), x = poly()
  const h = x, l = x
  poly_rq_sum_zero_frombytes(h, p)
  poly_rq_mul(t, r, h)
  poly_lift(l, y)
  for (let i = 0; i < ntru_n; i++) {
    t[i] += l[i]
  }
  poly_sq_tobytes(c, t)
}

function decrypts (t, o, s) {
  const x1 = poly(), x2 = poly(), x3 = poly(), x4 = poly()
  const b = x1, c = x1, cf = x3, f = x2, i = x3, j = x3, l = x2, m = x4, mf = x2, r = x4
  poly_rq_sum_zero_frombytes(c, t)
  poly_s3_frombytes(f, s)
  poly_z3_to_zq(f)
  poly_rq_mul(cf, c, f)
  poly_rq_to_s3(mf, cf)
  poly_s3_frombytes(i, s, trinary_bytes)
  poly_s3_mul(m, mf, i)
  poly_s3_tobytes(o, m, trinary_bytes)
  poly_lift(l, m)
  for (let i = 0; i < ntru_n; i++) {
    b[i] = c[i] - l[i]
  }
  poly_sq_frombytes(j, s, private_bytes)
  poly_sq_mul(r, b, j)
  poly_trinary_zq_to_z3(r)
  poly_s3_tobytes(o, r)
}

function pack (a) {
  let b = 0, c = a.length, d = []
  while (b < c) {
    d.push(a[b++] ^ a[b++] << 8 ^ a[b++] << 16 ^ a[b++] << 24)
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
  let i = uint32(a16).map((c, b) => a[b] | a0 + a[b + a32] | a0),
      j = uint32(a16).map((c, b) => a[b + a16] | a0 + a[b + a48] | a0)
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

  const p = 64n, q = g / p
  i = o(n(i) + q, uint32(a16))
  j = o(n(j) + q, uint32(a16))
  m = g % p
  a.set(unpack(l()).slice(num(m), num(h - g + m)))
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
  while (a.length > a128) {
    a = [...expand(a.slice(a0, a128), a0, a64), ...a.slice(a128)]
  }
  return expand(a, a0, h)
}

function crypto_kem_keypair (p, s) {
  keypair(p, s)
}

function crypto_kem_enc (c, k, p) {
  const r = poly(), y = poly()
  sample_rm(r, y)
  const o = uint8(private_bytes)
  poly_s3_tobytes(o, r)
  poly_s3_tobytes(o, y, trinary_bytes)
  k.set(reduce(o, 32))
  poly_z3_to_zq(r)
  encrypts(c, r, y, p)
}

function crypto_kem_dec (k, c, s) {
  const o = uint8(private_bytes)
  decrypts(c, o, s)
  k.set(reduce(o, 32))
}

priv = uint8(secret_bytes)
pub = uint8(public_bytes)
crypto_kem_keypair(pub, priv)
ciph = uint8(cipher_bytes)
key0 = uint8(shared_bytes)
crypto_kem_enc(ciph, key0, pub)
key1 = uint8(shared_bytes)
crypto_kem_dec(key1, ciph, priv)
key0.toString() == key1.toString()