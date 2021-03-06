include "./tree/incrementalQuinTree.circom";
include "../node_modules/circomlib/circuits/pedersen.circom";
include "../node_modules/circomlib/circuits/mimcsponge.circom";
include "../node_modules/circomlib/circuits/bitify.circom";
include "../node_modules/circomlib/circuits/eddsamimcsponge.circom";
include "../node_modules/circomlib/circuits/babyjub.circom";
include "../node_modules/circomlib/circuits/mux1.circom";
include "../node_modules/circomlib/circuits/poseidon.circom";
include "../node_modules/circomlib/circuits/comparators.circom";


template CalculateIdentityCommitment(IDENTITY_PK_SIZE_IN_BITS, NULLIFIER_TRAPDOOR_SIZE_IN_BITS) {
  signal input identity_pk[IDENTITY_PK_SIZE_IN_BITS];
  signal input identity_nullifier[NULLIFIER_TRAPDOOR_SIZE_IN_BITS];
  signal input identity_trapdoor[NULLIFIER_TRAPDOOR_SIZE_IN_BITS];

  signal output out;

  // identity commitment is a pedersen hash of (identity_pk, identity_nullifier, identity_trapdoor), each element padded up to 256 bits
  component identity_commitment = Pedersen(3*256);
  for (var i = 0; i < 256; i++) {
    if (i < IDENTITY_PK_SIZE_IN_BITS) {
      identity_commitment.in[i] <== identity_pk[i];
    } else {
      identity_commitment.in[i] <== 0;
    }

    if (i < NULLIFIER_TRAPDOOR_SIZE_IN_BITS) {
      identity_commitment.in[i + 256] <== identity_nullifier[i];
      identity_commitment.in[i + 2*256] <== identity_trapdoor[i];
    } else {
      identity_commitment.in[i + 256] <== 0;
      identity_commitment.in[i + 2*256] <== 0;
    }
  }

  out <== identity_commitment.out[0];
}

template CalculateNullifier(nInputs) {
  signal input inputs[nInputs];
  signal output out;

  component hasher = Poseidon(nInputs);
  for (var i = 0; i < nInputs; i ++) {
    hasher.inputs[i] <== inputs[i];
  }
  out <== hasher.out;
}

// n_levels must be < 32
template Semaphore(n_levels) {

    // BEGIN constants

    var IDENTITY_PK_SIZE_IN_BITS = 254;
    var NULLIFIER_TRAPDOOR_SIZE_IN_BITS = 248;
    var EXTERNAL_NULLIFIER_SIZE_IN_BITS = 232;

    var LEAVES_PER_NODE = 5;
    var LEAVES_PER_PATH_LEVEL = LEAVES_PER_NODE - 1;

    // END constants

    // BEGIN signals    
    signal input signal_hash;
    signal input external_nullifier;
    
    signal private input fake_zero;

    // mimc vector commitment
    signal private input identity_pk[2];
    signal private input identity_nullifier;
    signal private input identity_trapdoor;
    signal private input path_elements[n_levels][LEAVES_PER_PATH_LEVEL];
    signal private input identity_path_index[n_levels];

    // signature on (external nullifier, signal_hash) with identity_pk
    signal private input auth_sig_r[2];
    signal private input auth_sig_s;

    // mimc hash
    signal output root;
    signal output nullifiers_hash;
    // signal output id_comm;

    // END signals

    fake_zero === 0;

    component verify_identity_pk_on_curve = BabyCheck();
    verify_identity_pk_on_curve.x <== identity_pk[0];
    verify_identity_pk_on_curve.y <== identity_pk[1];

    component verify_auth_sig_r_on_curve = BabyCheck();
    verify_auth_sig_r_on_curve.x <== auth_sig_r[0];
    verify_auth_sig_r_on_curve.y <== auth_sig_r[1];

    // get a prime subgroup element derived from identity_pk
    component dbl1 = BabyDbl();
    dbl1.x <== identity_pk[0];
    dbl1.y <== identity_pk[1];
    component dbl2 = BabyDbl();
    dbl2.x <== dbl1.xout;
    dbl2.y <== dbl1.yout;
    component dbl3 = BabyDbl();
    dbl3.x <== dbl2.xout;
    dbl3.y <== dbl2.yout;

    component identity_nullifier_bits = Num2Bits(NULLIFIER_TRAPDOOR_SIZE_IN_BITS);
    identity_nullifier_bits.in <== identity_nullifier;

    component identity_trapdoor_bits = Num2Bits(NULLIFIER_TRAPDOOR_SIZE_IN_BITS);
    identity_trapdoor_bits.in <== identity_trapdoor;

    component identity_pk_0_bits = Num2Bits_strict();
    identity_pk_0_bits.in <== dbl3.xout;

    // BEGIN identity commitment
    component identity_commitment = CalculateIdentityCommitment(IDENTITY_PK_SIZE_IN_BITS, NULLIFIER_TRAPDOOR_SIZE_IN_BITS);
    for (var i = 0; i < IDENTITY_PK_SIZE_IN_BITS; i++) {
      identity_commitment.identity_pk[i] <== identity_pk_0_bits.out[i];
    }
    for (var i = 0; i < NULLIFIER_TRAPDOOR_SIZE_IN_BITS; i++) {
      identity_commitment.identity_nullifier[i] <== identity_nullifier_bits.out[i];
      identity_commitment.identity_trapdoor[i] <== identity_trapdoor_bits.out[i];
    }
    // END identity commitment

    // BEGIN TREE

    var i;
    var j;
    component inclusionProof = QuinTreeInclusionProof(n_levels);
    inclusionProof.leaf <== identity_commitment.out;

    for (i = 0; i < n_levels; i++) {
      for (j = 0; j < LEAVES_PER_PATH_LEVEL; j++) {
        inclusionProof.path_elements[i][j] <== path_elements[i][j];
      }
      inclusionProof.path_index[i] <== identity_path_index[i];
    }

    root <== inclusionProof.root;

    // END TREE

    component nullifiers_hasher = CalculateNullifier(3);
    nullifiers_hasher.inputs[0] <== external_nullifier;
    nullifiers_hasher.inputs[1] <== identity_nullifier;
    nullifiers_hasher.inputs[2] <== n_levels;

    nullifiers_hash <== nullifiers_hasher.out;

    // BEGIN verify sig
    component msg_hasher = MiMCSponge(2, 220, 1);
    msg_hasher.ins[0] <== external_nullifier;
    msg_hasher.ins[1] <== signal_hash;
    msg_hasher.k <== 0;

    component sig_verifier = EdDSAMiMCSpongeVerifier();
    (1 - fake_zero) ==> sig_verifier.enabled;
    identity_pk[0] ==> sig_verifier.Ax;
    identity_pk[1] ==> sig_verifier.Ay;
    auth_sig_r[0] ==> sig_verifier.R8x;
    auth_sig_r[1] ==> sig_verifier.R8y;
    auth_sig_s ==> sig_verifier.S;
    msg_hasher.outs[0] ==> sig_verifier.M;

    // END verify sig
}
