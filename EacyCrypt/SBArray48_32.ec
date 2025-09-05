from Jasmin require import JByte_array.

require import BArray32 BArray48.

clone SubByteArray as SBArray48_32  with theory Asmall <= BArray32,
                                         theory Abig <= BArray48.
