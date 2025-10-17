from Jasmin require import JByte_array.

require import BArray32 BArray4800.

clone SubByteArray as SBArray4800_32  with theory Asmall <= BArray32,
                                           theory Abig <= BArray4800.
