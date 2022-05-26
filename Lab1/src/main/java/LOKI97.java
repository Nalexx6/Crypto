import java.security.InvalidKeyException;
import cryptix.util.core.ArrayUtil;
import cryptix.util.core.Hex;

public final class LOKI97 {
    /** Number of bytes in a data-block. */
    static final int BLOCK_SIZE = 16;

    /** Number of rounds for the algorithm. */
    static final int ROUNDS = 16;

    /** Number of subkeys used by the algorithm. */
    static final int NUM_SUBKEYS = 3 * ROUNDS;

    /** Constant value for Delta which is used in the key schedule */
    private static final long DELTA = 0x9E3779B97F4A7C15L;

    /** Generator polynomial for S-box S1, in GF(2<sup>13</sup>). */
    private static final int S1_GEN = 0x2911;

    /** Size of S-box S1, for 13-bit inputs. */
    static final int S1_SIZE = 0x2000;

    /** Table of pre-computed S-box S1 values. */
    static final byte[] S1 = new byte[S1_SIZE];

    /** Generator polynomial for S-box S2, in GF(2<sup>11</sup>). */
    private static final int S2_GEN = 0xAA7;

    /** Size of S-box S2, for 11-bit inputs. */
    static final int S2_SIZE = 0x800;

    /** Table of pre-computed S-box S2 values. */
    static final byte[] S2 = new byte[S2_SIZE];

    /**
     * Table specifying the pre-computed permutation P. Note:<ul>
     * <li> precompute permutations for lowest 8 bits only, since the
     *      remainder of the permutation is related to it by successive
     *      right shifts for each successive input byte.
     * <li> value of P is a 64-bit wide (long) mask of the permuted input
     *      value.</ul>
     */
    static final long[] P = new long[0x100];

    public LOKI97(){
        //
        // precompute S-box tables for S1 and S2
        //
        System.out.println("Static init of precomputing tables");
        final int S1_MASK = S1_SIZE - 1; // mask to select S1 input bits
        final int S2_MASK = S2_SIZE - 1; // mask to select S2 input bits

        for (int i = 0; i < S1_SIZE; i++) { // for all S1 inputs
            int b = i ^ S1_MASK; // compute input value
            S1[i] = exp3(b, S1_GEN, S1_SIZE); // compute fn value
        }
        for (int i = 0; i < S2_SIZE; i++) { // for all S2 inputs
            int b = i ^ S2_MASK; // compute input value
            S2[i] = exp3(b, S2_GEN, S2_SIZE); // compute fn value
        }
        //
        // initialising expanded permutation P table (for lowest byte only)
        //   Permutation P maps input bits [63..0] to outputs bits:
        //   [56, 48, 40, 32, 24, 16,  8, 0,
        //    57, 49, 41, 33, 25, 17,  9, 1,
        //    58, 50, 42, 34, 26, 18, 10, 2,
        //    59, 51, 43, 35, 27, 19, 11, 3,
        //    60, 52, 44, 36, 28, 20, 12, 4,
        //    61, 53, 45, 37, 29, 21, 13, 5,
        //    62, 54, 46, 38, 30, 22, 14, 6,
        //    63, 55, 47, 39, 31, 23, 15, 7]  <- this row only used for table
        //  However, since it is so regular, can construct it on the fly
        //
        for (int i = 0; i < 0x100; i++) { // loop over all 8-bit inputs
            long pval = 0L;
            // for each input bit permute to specified output position
            for (int j = 0, k = 7; j < 8; j++, k += 8)
                pval |= (long)((i >>> j) & 0x1) << k;
            P[i] = pval;
        }
    }

    /**
     * Returns a byte residue of base b to power 3 mod g in GF(2^n).
     *
     * @param b  Base of exponentiation, the exponent being always 3.
     * @param g  Irreducible polynomial generating Galois Field (GF(2^n)).
     * @param n  Size of the galois field.
     * @return (b ** 3) mod g.
     */
    static byte exp3 (int b, int g, int n) {
        if (b == 0)
            return 0;
        int r = b;            // r = b ** 1
        b = mult(r, b, g, n); // r = b ** 2
        r = mult(r, b, g, n); // r = b ** 3
        return (byte) r;
    }

    /**
     * Returns the product of two binary numbers a and b, using the
     * generator g as the modulus: p = (a * b) mod g. g Generates a
     * suitable Galois Field in GF(2^n).
     *
     * @param a  First multiplicand.
     * @param b  Second multiplicand.
     * @param g  Irreducible polynomial generating Galois Field.
     * @param n  Size of the galois field.
     * @return (a * b) mod g.
     */
    static int mult (int a, int b, int g, int n) {
        int p = 0;
        while (b != 0) {
            if ((b & 0x01) != 0)
                p ^= a;
            a <<= 1;
            if (a >= n)
                a ^= g;
            b >>>= 1;
        }
        return p;
    }

    private static long pack(byte[] k, int i){
        return (k[i++] & 0xFFL) << 56 | (k[i++] & 0xFFL) << 48 |
                (k[i++] & 0xFFL) << 40 | (k[i++] & 0xFFL) << 32 |
                (k[i++] & 0xFFL) << 24 | (k[i++] & 0xFFL) << 16 |
                (k[i++] & 0xFFL) <<  8 | (k[i] & 0xFFL);
    }

    private static byte[] unpack(long L, long R){
        return new byte[]{
                (byte)(R >>> 56), (byte)(R >>> 48),
                (byte)(R >>> 40), (byte)(R >>> 32),
                (byte)(R >>> 24), (byte)(R >>> 16),
                (byte)(R >>>  8), (byte) R,
                (byte)(L >>> 56), (byte)(L >>> 48),
                (byte)(L >>> 40), (byte)(L >>> 32),
                (byte)(L >>> 24), (byte)(L >>> 16),
                (byte)(L >>>  8), (byte) L
        };
    }

    /**
     * Expand a user-supplied key material into a LOKI97 session key.
     *
     * @param k  The 128/192/256-bit user-key to use.
     * @exception  InvalidKeyException if the key is invalid.
     */
    public static synchronized Object makeKey (byte[] k) throws InvalidKeyException {
        if (k == null)
            throw new InvalidKeyException("Empty key");
        if (!(k.length == 16 || k.length == 24 || k.length == 32))
             throw new InvalidKeyException("Incorrect key length");

        long[] SK = new long[NUM_SUBKEYS];	// array of subkeys

        long deltan = DELTA;			// multiples of delta

        long k4, k3, k2, k1;			// key schedule 128-bit entities
        long f_out;				// fn f output value for debug

        k4 = pack(k, 0);
        k3 = pack(k, 8);
        if (k.length == 16) {   // 128-bit key - call fn f twice to gen 256 bits
            k2 = f(k3, k4);
            k1 = f(k4, k3);
        } else {                // 192 or 256-bit key - pack k2 from key data
            k2 = pack(k, 16);
            if (k.length == 24) // 192-bit key - call fn f once to gen 256 bits
                k1 = f(k4, k3);
            else                // 256-bit key - pack k1 from key data
                k1 = pack(k, 24);
        }
        
        // iterate over all LOKI97 rounds to generate the required subkeys
        for (int i = 0; i < NUM_SUBKEYS; i++) {
            f_out = f(k1 + k3 + deltan, k2);
            SK[i] = k4 ^ f_out;		// compute next subkey value using fn f
            k4 = k3;			// exchange the other words around
            k3 = k2;
            k2 = k1;
            k1 = SK[i];
            deltan += DELTA;		// next multiple of delta
        }

        return SK;
    }

    /**
     * Encrypt exactly one block of plaintext.
     *
     * @param in          The plaintext.
     * @param inOffset    Index of in from which to start considering data.
     * @param sessionKey  The session key to use for encryption.
     * @return The ciphertext generated from a plaintext using the session key.
     */
    public static byte[] blockEncrypt (byte[] in, int inOffset, Object sessionKey) {
        long[] SK = (long[]) sessionKey;	// local ref to session key

        long L = pack(in, inOffset);
        long R = pack(in, inOffset + 8);

        // compute all rounds for this 1 block
        long nR, f_out;
        int k = 0;
        for (int i = 0; i < ROUNDS; i++) {
            nR = R + SK[k++];
            f_out = f(nR, SK[k++]);
            nR += SK[k++];
            R = L ^ f_out;
            L = nR;
        }

        return unpack(L, R);
    }

    /**
     * Decrypt exactly one block of ciphertext.
     *
     * @param in          The ciphertext.
     * @param inOffset    Index of in from which to start considering data.
     * @param sessionKey  The session key to use for decryption.
     * @return The plaintext generated from a ciphertext using the session key.
     */
    public static byte[]
    blockDecrypt (byte[] in, int inOffset, Object sessionKey) {
        long[] SK = (long[]) sessionKey;

        long L = pack(in, inOffset);
        long R = pack(in, inOffset + 8);

        // compute all rounds for this 1 block
        long nR, f_out;
        int k = NUM_SUBKEYS - 1;
        for (int i = 0; i < ROUNDS; i++) {
            nR = R - SK[k--];
            f_out = f(nR, SK[k--]);
            nR -= SK[k--];
            R = L ^ f_out;
            L = nR;
        }

        return unpack(L, R);
    }

    /**
     * Complex highly non-linear round function
     * f(A,B) = Sb(P(Sa(E(KP(A,hi(B))))),lo(B))
     *
     * @param A  64-bit input A
     * @param B  64-bit input B
     * @return The resulting 64-bit function value
     */
    private static long f (long A, long B) {
        // Intermediate values in the computation are:
        //   d = KP(A,B)
        //   e = P(Sa(d))
        //   f = Sb(e,B)

        // Compute d = KP(A,B), where KP is a keyed permutation used to 
        //    exchange corresponding bits in 32-bit words [Al,Ar] 
        //    based on the lower half of B (called Br) (swap if B bit is 1)
        //    KP(A,B) = ((Al & ~Br)|(Ar & Br)) | ((Ar & ~Br)|(Al & Br))

        int Al = (int)(A >>> 32);
        int Ar = (int) A;
        int Br = (int) B;
        long d = ((long)((Al & ~Br) | (Ar & Br)) << 32) |
                 ((long)((Ar & ~Br) | (Al & Br)) & 0xFFFFFFFFL);

        // Compute e = P(Sa(d))
        //    mask out each group of 12 bits for E
        //    then compute first S-box column [S1,S2,S1,S2,S2,S1,S2,S1]
        //    permuting output through P (with extra shift to build full P)

        long e = P[S1[(int)((d >>> 56 | d << 8) & 0x1FFF)] & 0xFF] >>> 7 |
                 P[S2[(int)((d >>> 48)          &  0x7FF)] & 0xFF] >>> 6 |
                 P[S1[(int)((d >>> 40)          & 0x1FFF)] & 0xFF] >>> 5 |
                 P[S2[(int)((d >>> 32)          &  0x7FF)] & 0xFF] >>> 4 |
                 P[S2[(int)((d >>> 24)          &  0x7FF)] & 0xFF] >>> 3 |
                 P[S1[(int)((d >>> 16)          & 0x1FFF)] & 0xFF] >>> 2 |
                 P[S2[(int)((d >>>  8)          &  0x7FF)] & 0xFF] >>> 1 |
                 P[S1[(int)( d                  & 0x1FFF)] & 0xFF];

        // Compute f = Sb(e,B)
        //    where the second S-box column is [S2,S2,S1,S1,S2,S2,S1,S1]
        //    for each S, lower bits come from e, upper from upper half of B

        return (S2[(int)(((e>>>56) & 0xFF) | ((B>>>53) &  0x700))] & 0xFFL) << 56 |
        (S2[(int)(((e>>>48) & 0xFF) | ((B>>>50) &  0x700))] & 0xFFL) << 48 |
        (S1[(int)(((e>>>40) & 0xFF) | ((B>>>45) & 0x1F00))] & 0xFFL) << 40 |
        (S1[(int)(((e>>>32) & 0xFF) | ((B>>>40) & 0x1F00))] & 0xFFL) << 32 |
        (S2[(int)(((e>>>24) & 0xFF) | ((B>>>37) &  0x700))] & 0xFFL) << 24 |
        (S2[(int)(((e>>>16) & 0xFF) | ((B>>>34) &  0x700))] & 0xFFL) << 16 |
        (S1[(int)(((e>>> 8) & 0xFF) | ((B>>>29) & 0x1F00))] & 0xFFL) <<  8 |
        (S1[(int)(( e       & 0xFF) | ((B>>>24) & 0x1F00))] & 0xFFL);
    }

    /** A basic symmetric encryption/decryption test for a given key size. */
    private boolean self_test (int keysize) {
        boolean ok = false;
        try {
            byte[] kb = new byte[keysize];
            byte[] pt = new byte[BLOCK_SIZE];
            int i;

            for (i = 0; i < keysize; i++)
                kb[i] = (byte) i;
            for (i = 0; i < BLOCK_SIZE; i++)
                pt[i] = (byte) i;


            System.out.println("==========");
            System.out.println();
            System.out.println("KEYSIZE="+(8*keysize));
            System.out.println("KEY="+ Hex.toString(kb));
            System.out.println();
            
            Object key = makeKey(kb);
            
            byte[] ct =  blockEncrypt(pt, 0, key);
            byte[] cpt = blockDecrypt(ct, 0, key);

            ok = ArrayUtil.areEqual(pt, cpt);
            if (!ok)
                throw new RuntimeException("Symmetric operation failed");
        } catch (Exception x) {
            x.printStackTrace();
        }

        return ok;
    }

    /** Encryption/decryption test using the standard single triple.
     *
     *  @return  true if test successful
     */
    public boolean triple_test() {
        boolean result = false;
        boolean enok = true, deok = true;
        byte[] keyx = {				// Standard LOKI97 Single Triple
              0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15,
             16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31};
        byte[] plain = {
             0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15};
        byte[] cipher = Hex.fromString("75080E359F10FE640144B35C57128DAD");
        byte[] temp;

        try {
            System.out.println("SelfTest");
            // Display and verify single triple test value
            System.out.println("   key: " + Hex.toString(keyx));
            System.out.println(" plain: " + Hex.toString(plain));
            System.out.println("cipher: " + Hex.toString(cipher));

            Object key = makeKey(keyx);
            temp =  blockEncrypt(plain, 0, key);	// Test encrypt
            if (! ArrayUtil.areEqual(temp, cipher)) enok = false;
            System.out.println("Test encrypt: " + Hex.toString(temp)+
            (enok ? "    GOOD" : "    FAILED"));

            temp = blockDecrypt(cipher, 0, key);	// Test decrypt
            if (! ArrayUtil.areEqual(temp, plain)) deok = false;
            System.out.println("Test decrypt: " + Hex.toString(temp)+
            (deok ? "    GOOD" : "    FAILED"));
            result = enok && deok;
        }
        catch (Exception ex) {
            System.out.println("Exception in triple-test: " + ex.getMessage());
            ex.printStackTrace();
        }

        return result;
    }

    public static void main (String[] args) {
        LOKI97 loki = new LOKI97();

        boolean result = loki.self_test(16);
        System.out.println("Self-test OK? " + result);

        result = loki.self_test(24);
        System.out.println("Self-test OK? " + result);

        result = loki.self_test(32);
        System.out.println("Self-test OK? " + result);

        result = loki.triple_test();
        System.out.println("triple-test OK? " + result);

    }
}
