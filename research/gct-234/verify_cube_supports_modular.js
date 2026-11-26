"use strict";

// Run: node verify_cube_supports_modular.js 50
// This verifies necessary conditions for a root of multiplicity >= 10 using
// an affine numerator H in the partial fraction expansion of Euler moments.
// At four equally spaced nodes of a disconnected support block, H(x)/S(x)
// must form a geometric progression; S is the nodal polynomial of the other
// two blocks. Here "disconnected" means no nodes in common with those blocks.
// Every eligible triple has at least one such block. Nonzero residues exclude
// triples. Exact integer tests resolve every surviving case.

function makeBlocks(degree) {
  const blocks = [];
  for (let a = 0; a < degree; a++) {
    for (let b = a + 1; b <= degree; b++) {
      const first = 3 * a;
      const gap = b - a;
      blocks.push([first, first + gap, first + 2 * gap, first + 3 * gap]);
    }
  }
  return blocks;
}

function precompute(blocks, prime) {
  const size = blocks.length;
  const common = new Int16Array(size * size);
  const values = new Uint16Array(4 * size * size);
  for (let i = 0; i < size; i++) {
    for (let j = 0; j < size; j++) {
      const pair = i * size + j;
      let shared = -1;
      for (let pos = 0; pos < 4; pos++) {
        const x = blocks[i][pos];
        let product = 1;
        for (const y of blocks[j]) product = product * (x - y) % prime;
        values[4 * pair + pos] = (product + prime) % prime;
        // Every nonzero difference is smaller than the prime in absolute value.
        if (product === 0) shared = shared === -1 ? x : -2;
      }
      common[pair] = shared; // -1: disjoint; -2: at least two common nodes
    }
  }
  return {common, values};
}

function modularRow(i, j, k, collision, blocks, values, prime) {
  const size = blocks.length;
  const left = 4 * (i * size + j);
  const right = 4 * (i * size + k);
  const s0 = values[left] * values[right] % prime;
  const s1 = values[left + 1] * values[right + 1] % prime;
  const s2 = values[left + 2] * values[right + 2] % prime;
  const s3 = values[left + 3] * values[right + 3] % prime;
  // Write H at this block's four nodes as Y, Y+Z, Y+2Z, Y+3Z.
  // The two adjacent geometric-progression tests are homogeneous quadratics
  // A*Y^2+2*A*Y*Z+C*Z^2, and E*Y^2+4*E*Y*Z+F*Z^2.
  const C = s0 * s2 % prime;
  const A = C - s1 * s1 % prime;
  const cross = s1 * s3 % prime;
  const E = cross - s2 * s2 % prime;
  const F = 3 * E + cross;
  if (collision >= 0) {
    // A repeated pole forces H(collision)=0. Up to nonzero scale H(x)=x-collision.
    const Y = blocks[i][0] - collision;
    const Z = blocks[i][1] - blocks[i][0];
    return (A * Y * (Y + 2 * Z) + C * Z * Z) % prime === 0 &&
      ((E * Y + 4 * E * Z) * Y + F * Z * Z) % prime === 0;
  }
  // The two homogeneous quadratics must have a common projective root.
  const af_cd = (A * F - C * E) % prime;
  const ae_bd = 2 * A * E % prime;
  const bf_ce = (2 * A * F - 4 * C * E) % prime;
  return (af_cd * af_cd - ae_bd * bf_ce) % prime === 0;
}

function exactPass(ids, blocks, common) {
  const triple = ids.map(i => blocks[i]);
  const size = blocks.length;
  const collision = Math.max(common[ids[0]*size+ids[1]],
    common[ids[0]*size+ids[2]], common[ids[1]*size+ids[2]]);
  const prior = [];
  for (let i = 0; i < 3; i++) {
    const nodes = triple[i];
    if (nodes.includes(collision)) continue;
    const others = triple[(i+1)%3].concat(triple[(i+2)%3]);
    const weights = nodes.map(x => others.reduce((p, y) => p * BigInt(x-y), 1n));
    for (let pos = 0; pos < 2; pos++) {
      const [x,y,z] = nodes.slice(pos, pos+3).map(BigInt);
      const [u,v,w] = weights.slice(pos, pos+3);
      // Use global affine coordinates H(x)=h0 + h1*x in the exact calculation.
      const A = u*w-v*v;
      const B = 2n*y*u*w-(x+z)*v*v;
      const C = y*y*u*w-x*z*v*v;
      if (collision >= 0) {
        const c = BigInt(collision);
        if (A*c*c-B*c+C !== 0n) return false;
      }
      for (const [D,E,F] of prior) {
        if ((A*F-C*D)**2n !== (A*E-B*D)*(B*F-C*E)) return false;
      }
      prior.push([A,B,C]);
    }
  }
  return true;
}

function run(degree) {
  const prime = degree <= 83 ? 251 : 503;
  if (!Number.isInteger(degree) || degree < 1 || degree > 100) {
    throw new Error("Use an integer degree between 1 and 100.");
  }
  const start = Date.now();
  const blocks = makeBlocks(degree);
  const size = blocks.length;
  const {common, values} = precompute(blocks, prime);
  let eligible = 0, modularSurvivors = 0, exactSurvivors = 0;
  for (let i = 0; i < degree; i++) { // first block starts at original exponent 0
    for (let j = i+1; j < size; j++) {
      const ij = common[i*size+j];
      if (ij === -2) continue;
      for (let k = j+1; k < size; k++) {
        const ik = common[i*size+k], jk = common[j*size+k];
        if (ik === -2 || jk === -2 || Number(ij>=0)+Number(ik>=0)+Number(jk>=0)>1) continue;
        eligible++;
        if (ij >= 0) {
          if (!modularRow(k,i,j,ij,blocks,values,prime)) continue;
        } else if (ik >= 0) {
          if (!modularRow(j,i,k,ik,blocks,values,prime)) continue;
        } else if (jk >= 0) {
          if (!modularRow(i,j,k,jk,blocks,values,prime)) continue;
        } else if (!modularRow(i,j,k,-1,blocks,values,prime) ||
                   !modularRow(j,i,k,-1,blocks,values,prime) ||
                   !modularRow(k,i,j,-1,blocks,values,prime)) continue;
        modularSurvivors++;
        if (exactPass([i,j,k],blocks,common)) {
          exactSurvivors++;
          console.log("Necessary-test survivor:", blocks[i], blocks[j], blocks[k]);
        }
      }
    }
  }
  const seconds = (Date.now() - start) / 1000;
  console.log({degree, prime, eligible, modularSurvivors, exactSurvivors, seconds});
}

run(Number(process.argv[2] || 50));
