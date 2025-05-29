app "main"
    provides [main] to platform

requires {
    Cmd,
    Task.{ Task, await, map, after },
    Stdio.{ putStr, putErrStr },
    Str,
    List,
    Bitwise,
    Result,
    Num, # For U32, U64, and potentially byte conversion if not in Bitwise/List
}

# SHA-256 Initial Hash Values (H0-H7)
# First 32 bits of the fractional parts of the square roots of the first 8 primes 2..19.
h0 : U32 = 0x6a09e667
h1 : U32 = 0xbb67ae85
h2 : U32 = 0x3c6ef372
h3 : U32 = 0xa54ff53a
h4 : U32 = 0x510e527f
h5 : U32 = 0x9b05688c
h6 : U32 = 0x1f83d9ab
h7 : U32 = 0x5be0cd19

initialHashValues : List U32
initialHashValues = [h0, h1, h2, h3, h4, h5, h6, h7]

# SHA-256 Round Constants (K)
# First 32 bits of the fractional parts of the cube roots of the first 64 primes 2..311.
k : List U32
k = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

# SHA-256 Helper Functions (Bitwise Operations on U32)

# Rotate right
rotr : U32, U32 -> U32
rotr = \n, x ->
    # Ensure n is within 0-31 for U32
    actualN = n % 32
    if actualN == 0 then
        x
    else
        Bitwise.shiftRightZfBy x actualN |> Bitwise.or_ (Bitwise.shiftLeftBy x (32 - actualN))

# Shift right (logical)
shr : U32, U32 -> U32
shr = \n, x ->
    # Ensure n is within 0-31 for U32
    actualN = n % 32
    if actualN == 0 then
        x
    else
        Bitwise.shiftRightZfBy x actualN

# Choose
ch : U32, U32, U32 -> U32
ch = \x, y, z ->
    Bitwise.xor (Bitwise.and_ x y) (Bitwise.and_ (Bitwise.not_ x) z)

# Majority
maj : U32, U32, U32 -> U32
maj = \x, y, z ->
    Bitwise.xor (Bitwise.and_ x y) (Bitwise.xor (Bitwise.and_ x z) (Bitwise.and_ y z))

# Big Sigma 0
bigSigma0 : U32 -> U32
bigSigma0 = \x ->
    Bitwise.xor (rotr 2 x) (Bitwise.xor (rotr 13 x) (rotr 22 x))

# Big Sigma 1
bigSigma1 : U32 -> U32
bigSigma1 = \x ->
    Bitwise.xor (rotr 6 x) (Bitwise.xor (rotr 11 x) (rotr 25 x))

# Small Sigma 0
smallSigma0 : U32 -> U32
smallSigma0 = \x ->
    Bitwise.xor (rotr 7 x) (Bitwise.xor (rotr 18 x) (shr 3 x))

# Small Sigma 1
smallSigma1 : U32 -> U32
smallSigma1 = \x ->
    Bitwise.xor (rotr 17 x) (Bitwise.xor (rotr 19 x) (shr 10 x))

# Helper to convert U64 to a List U8 (big-endian)
u64ToBigEndianBytes : U64 -> List U8
u64ToBigEndianBytes = \val ->
    [
        Bitwise.shiftRightZfBy val 56 |> Num.toU8, # MSB
        Bitwise.shiftRightZfBy val 48 |> Num.toU8,
        Bitwise.shiftRightZfBy val 40 |> Num.toU8,
        Bitwise.shiftRightZfBy val 32 |> Num.toU8,
        Bitwise.shiftRightZfBy val 24 |> Num.toU8,
        Bitwise.shiftRightZfBy val 16 |> Num.toU8,
        Bitwise.shiftRightZfBy val 8 |> Num.toU8,
        Bitwise.shiftRightZfBy val 0 |> Num.toU8, # LSB
    ]

# SHA-256 Message Padding Function
padMessage : List U8 -> List U8
padMessage = \message ->
    # l is the original message length in bits
    l = List.len message |> Num.toU64 |> Num.mulBy 8
    
    # Append the bit '1' (0x80 byte)
    padded = List.append message 0x80

    # Append k zero bits (kZeroBytes zero bytes)
    # L + 1 + k ≡ 448 (mod 512)
    # (messageLengthInBytes * 8) + 8 + kZeroBits ≡ 448 (mod 512)
    # messageLengthInBytes + 1 + kZeroBytes ≡ 56 (mod 64)
    # So, current length in bytes is List.len padded
    # We need total length to be X such that X % 64 == 56
    
    currentLenBytes = List.len padded
    kZeroBytes =
        val = (56 - (currentLenBytes % 64) + 64) % 64
        val

    # Append kZeroBytes of 0x00
    zeros = List.walk (List.range Identity kZeroBytes) [] (\lst, _ -> List.append lst 0u8)
    intermediatePadded = List.concat padded zeros # Assuming List.concat appends two lists
    
    # Append L (original message length in bits) as a 64-bit big-endian integer
    lengthBytes = u64ToBigEndianBytes l
    List.concat intermediatePadded lengthBytes # Assuming List.concat appends two lists

# Helper to convert a 4-byte slice of List U8 to U32 (big-endian)
# Assumes the slice always has 4 bytes.
listU8ToU32BE : List U8, Nat -> U32
listU8ToU32BE = \byteList, offset ->
    b0 = List.getUnsafe byteList offset     |> Num.toU32 # MSB
    b1 = List.getUnsafe byteList (offset + 1) |> Num.toU32
    b2 = List.getUnsafe byteList (offset + 2) |> Num.toU32
    b3 = List.getUnsafe byteList (offset + 3) |> Num.toU32 # LSB

    Bitwise.or_ (Bitwise.shiftLeftBy b0 24) (
        Bitwise.or_ (Bitwise.shiftLeftBy b1 16) (
            Bitwise.or_ (Bitwise.shiftLeftBy b2 8) b3
        )
    )

# Helper to convert a U32 to a 4-byte List U8 (big-endian)
u32ToBigEndianBytes : U32 -> List U8
u32ToBigEndianBytes = \val ->
    [
        Bitwise.shiftRightZfBy val 24 |> Num.toU8, # MSB
        Bitwise.shiftRightZfBy val 16 |> Num.toU8,
        Bitwise.shiftRightZfBy val 8  |> Num.toU8,
        Bitwise.shiftRightZfBy val 0  |> Num.toU8  # LSB
    ]

# Core SHA-256 Hashing Function
sha256Once : List U8 -> List U8
sha256Once = \inputBytes ->
    paddedMessage = padMessage inputBytes

    # Initialize hash state
    hashState = initialHashValues # This is List U32

    # Process message in 512-bit (64-byte) chunks
    numChunks = List.len paddedMessage // 64

    finalHashState =
        List.range Identity numChunks # Iterate from 0 to numChunks-1
        |> List.walk hashState \currentHashes, chunkIndex ->
            chunkStart = chunkIndex * 64
            
            # 1. Create message schedule w : List U32 (size 64)
            wInitial = List.map (List.range Identity 16) \i ->
                listU8ToU32BE paddedMessage (chunkStart + (i * 4))
            
            wFull =
                List.range Identity (64 - 16) # Iterate 48 times for indices 16..63
                |> List.walk wInitial \currentW, iVal -> # iVal from 0 to 47
                    i = iVal + 16 # current index in wFull we are calculating (16 to 63)
                    
                    term1 = List.getUnsafe currentW (i-2) |> smallSigma1
                    term2 = List.getUnsafe currentW (i-7)
                    term3 = List.getUnsafe currentW (i-15) |> smallSigma0
                    term4 = List.getUnsafe currentW (i-16)
                    
                    val = term1 + term2 + term3 + term4 # U32 addition wraps
                    List.append currentW val

            # 2. Initialize working variables a, b, c, d, e, f, g, h
            varsRecord = {
                a: List.getUnsafe currentHashes 0,
                b: List.getUnsafe currentHashes 1,
                c: List.getUnsafe currentHashes 2,
                d: List.getUnsafe currentHashes 3,
                e: List.getUnsafe currentHashes 4,
                f: List.getUnsafe currentHashes 5,
                g: List.getUnsafe currentHashes 6,
                h: List.getUnsafe currentHashes 7,
            }

            # 3. Compression Loop (64 rounds)
            finalVarsRecord =
                List.range Identity 64 # Iterate t from 0 to 63
                |> List.walk varsRecord \currentVars, t ->
                    s1 = bigSigma1 currentVars.e
                    chVal = ch currentVars.e currentVars.f currentVars.g
                    k_t = List.getUnsafe k t       # Round constant
                    w_t = List.getUnsafe wFull t   # Message schedule word
                    
                    temp1 = currentVars.h + s1 + chVal + k_t + w_t

                    s0 = bigSigma0 currentVars.a
                    majVal = maj currentVars.a currentVars.b currentVars.c
                    temp2 = s0 + majVal

                    {
                        a: temp1 + temp2,
                        b: currentVars.a,
                        c: currentVars.b,
                        d: currentVars.c,
                        e: currentVars.d + temp1,
                        f: currentVars.e,
                        g: currentVars.f,
                        h: currentVars.g,
                    }
            
            # 4. Add compressed chunk to current hash values
            [
                (List.getUnsafe currentHashes 0) + finalVarsRecord.a,
                (List.getUnsafe currentHashes 1) + finalVarsRecord.b,
                (List.getUnsafe currentHashes 2) + finalVarsRecord.c,
                (List.getUnsafe currentHashes 3) + finalVarsRecord.d,
                (List.getUnsafe currentHashes 4) + finalVarsRecord.e,
                (List.getUnsafe currentHashes 5) + finalVarsRecord.f,
                (List.getUnsafe currentHashes 6) + finalVarsRecord.g,
                (List.getUnsafe currentHashes 7) + finalVarsRecord.h
            ] # New hash state for next chunk

    # 5. Output: Concatenate final hash_state (h0..h7) into a List U8
    List.walk finalHashState [] \byteList, hVal ->
        List.concat byteList (u32ToBigEndianBytes hVal)

# Double SHA-256 Function
doubleSha256 : Str -> List U8
doubleSha256 = \text ->
    # 1. Convert input string to List U8 using UTF-8 encoding
    utf8Bytes = Str.toUtf8 text

    # 2. Calculate the first SHA-256 hash
    hash1 = sha256Once utf8Bytes

    # 3. Calculate the second SHA-256 hash on the *binary output* of the first
    finalHash = sha256Once hash1

    # 4. Return the final hash (List U8)
    finalHash

# Convert a List U8 to a lowercase hexadecimal String
bytesToHexStr : List U8 -> Str
bytesToHexStr = \bytes ->
    hexChars = "0123456789abcdef" # Lookup string for hex characters
    hexCharsBytes = Str.toUtf8 hexChars # Convert once for efficiency

    toHex : U8 -> Str
    toHex = \byte ->
        highNibble = Bitwise.shiftRightZfBy byte 4
        lowNibble = Bitwise.and_ byte 0x0F # Mask to get the lower 4 bits
        
        # Nibbles are 0-15. Num.toNat converts U8 to Nat for indexing.
        # List.getUnsafe is used as indices are guaranteed to be valid.
        highCharByte = List.getUnsafe hexCharsBytes (Num.toNat highNibble)
        lowCharByte  = List.getUnsafe hexCharsBytes (Num.toNat lowNibble)

        # Str.fromUtf8 expects List U8.
        # Result.withDefault is a fallback, though not strictly needed if hexChars is ASCII.
        Str.fromUtf8 [highCharByte, lowCharByte] |> Result.withDefault ""

    # Iterate over each byte, convert to 2 hex chars, and join.
    List.walk bytes Str.empty \accStr, byte ->
        Str.concat accStr (toHex byte)

# Main application entry point
main : Task {} _
main =
    Cmd.argv
    |> Task.andThen \args ->
        argsLen = List.len args
        # Expects 2 arguments: program name and input text
        # e.g. ["./double_sha256", "hello world"]
        if argsLen != 2 then
            # Error case: incorrect number of arguments
            errorTask = 
                Task.await (Stdio.putErrStr "Usage: ./double_sha256 <text_to_hash>") \_ ->
                Task.await (Cmd.exitCode 1) \_ ->
                    Task.ok {} # Fulfils Task {} _
            errorTask
        else
            # Success case: correct number of arguments
            when List.get args 1 is
                Ok inputText ->
                    hashedBytes = doubleSha256 inputText
                    hexOutput = bytesToHexStr hashedBytes
                    
                    successTask =
                        Task.await (Stdio.putStr hexOutput) \_ ->
                        Task.await (Cmd.exitCode 0) \_ ->
                            Task.ok {} # Fulfils Task {} _
                    successTask
                Err _ ->
                    # Error case: List.get failed (should not happen with length check)
                    # This specific error message helps distinguish from the usage error.
                    Task.await (Stdio.putErrStr "Error: Could not retrieve input text argument unexpectedly.") \_ ->
                    Task.await (Cmd.exitCode 1) \_ ->
                        Task.ok {}
