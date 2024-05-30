include "Io.dfy"
include "Find.dfy"

// check if a character is a digit
predicate isDigit(c: char) {
  '0' <= c <= '9'
}

// convert a digit character to its numeric value
function digit(c: char): nat
  requires isDigit(c)
  ensures 0 <= digit(c) <= 9
{
  (c - '0') as nat
}

// convert a numeric value (0-9) to its corresponding digit character
function digitChar(n: nat): char
  requires n < 10
  ensures '0' <= digitChar(n) <= '9'
{
  n as char + '0'
}

// check if a string represents a natural number
predicate isNatStr(s: string)
{
  forall c | c in s :: isDigit(c)
}

// convert a string representing a natural number to its numeric value
function strToNat(s: string): nat
  requires isNatStr(s)
{
  if |s| == 0 then 0 else strToNat(s[..|s| - 1]) * 10 + digit(s[0])
}

// convert a natural number to its string representation
function natToStr(i: nat): string
  ensures isNatStr(natToStr(i))
{
  if i < 10 then [digitChar(i)] else natToStr(i / 10) + [digitChar(i % 10)]
}

// check if a string represents an integer
predicate isIntStr(s: string)
{
  |s| > 0 && (s[0] == '-' || isDigit(s[0])) && isNatStr(s[1..])
}

// convert a string representing an integer to its numeric value
function strToInt(s: string): int
  requires isIntStr(s)
{
  if s[0] == '-' then -(strToNat(s[1..]) as int) else strToNat(s)
}

// convert an integer to its string representation
function intToStr(i: int): string
  ensures isIntStr(intToStr(i))
{
  if i < 0 then ['-'] + natToStr(-i) else natToStr(i)
}

method {:main} Main(ghost env: HostEnvironment?)
  requires env != null && env.Valid() && env.ok.ok()
  modifies env.ok, env.files // necessário quando chama FileStream.Open
{
  // ====  1. Command-line arguments ===

  // check the number of command-line arguments
  var numArgs: uint32 := HostConstants.NumCommandLineArgs(env);
  if (numArgs != 4) { // TODO: 3 ou 4?
    print "Error: Expected 3 arguments, found ", numArgs, ". Usage: <K> <source_file> <destination_file>\n";
    return;
  }
  // get command-line arguments
  var kString: array<char> := HostConstants.GetCommandLineArg(1, env);
  var sourceFile: array<char> := HostConstants.GetCommandLineArg(2, env);
  var destFile: array<char> := HostConstants.GetCommandLineArg(3, env);

  // check if the first argument is a valid natural number
  if (!isNatStr(kString[..])) {
    print("Error: K must be a natural number\n");
    return;
  }

  var k := strToNat(kString[..]);

  //  ==== 2. Check file existence and open files  ====

  //  check if the destination file already exists
  var destFileExists: bool := FileStream.FileExists(destFile, env);
  if (destFileExists) {
    print("Error: Destination file already exists\n");
    return;
  }

  //  ==== 3. Read the source file, find the k-th smallest element, and write the result  ====

  // open the source file to read the numbers
  var okOpenSource, sourceFileStream := FileStream.Open(sourceFile, env);
  if (!okOpenSource) {
    print ("Error: Unable to open source file\n");
    return;
  }

  // get the length of the source file
  var okLength, fileLength := FileStream.FileLength(sourceFile, env);
  if (!okLength) {
    print ("Error: Unable to get file length\n");
    return;
  }

  // read integers from the source file
  var inputNumbers: seq<int> := [];
  var numberStr: string := [];
  var bytesRead: nat32 := 0;

  var readBuffer := new byte[fileLength];

  var okRead := sourceFileStream.Read(0, readBuffer, 0, fileLength);
  if (!okRead) {
    print("Error: Unable to read from source file\n");
    return;
  }

  // split the input by '\n'
  var numsStr := [];
  var currentNum := "";
  for i: int := 0 to readBuffer.Length
    invariant env.Valid() && env.ok.ok()
  {
    if (readBuffer[i] as char != '\n') {
      currentNum := currentNum + [readBuffer[i] as char];
    } else {
      if (currentNum != "") {
        numsStr := numsStr + [currentNum];
      }
      currentNum := "";
    }
  }

  // if the last number is not followed by a newline character
  if (currentNum != "") {
    numsStr := numsStr + [currentNum];
  }

  // convert the sequence of strings to a sequence of integers
  for i: int := 0 to |numsStr|
    invariant env.Valid() && env.ok.ok()
  {
    if (isIntStr(numsStr[i])) {
      inputNumbers := inputNumbers + [strToInt(numsStr[i])];
    } else {
      print("Error: Invalid integer in source file\n");
      return;
    }
  }

  // convert the sequence to an array
  var outputNumbers := new int[|inputNumbers|];
  for i: nat := 0 to |inputNumbers|
    invariant env.Valid() && env.ok.ok()
    modifies outputNumbers
  {
    outputNumbers[i] := inputNumbers[i];
  }

  // check if k is within the valid range
  if (k >= outputNumbers.Length) {
    print("Error: K must be between 0 and the input's length\n");
    return;
  }

  // find the k-th smallest element using the Find method
  var x := Find(outputNumbers, k);

  // convert outputNumbers to a string
  var outputStr := "";
  for i: nat := 0 to outputNumbers.Length
    invariant env.Valid() && env.ok.ok()
    // ensure that the character is within the valid range
    invariant forall c | c in outputStr :: c <= '\U{ff}'
  {
    outputStr := outputStr + intToStr(outputNumbers[i]) + "\n";
  }

  // convert the string to a byte array
  var outputBuffer := new byte[|outputStr|];
  for i: nat := 0 to |outputStr|
    invariant env.Valid() && env.ok.ok()
  {
    // this assert is required to prove that the character is within the valid range
    assert outputStr[i] in outputStr;
    outputBuffer[i] := outputStr[i] as byte;
  }

  // open the destination file to write the output
  var okOpenDest, destFileStream := FileStream.Open(destFile, env);
  if (!okOpenDest) {
    print ("Error: Unable to open destination file\n");
    return;
  }

  // ensure the length is within int32 range
  if (outputBuffer.Length >= 0x80000000) {
    print("Error: Output is too large\n");
    return;
  }

  // write the output to the destination file
  var okWrite := destFileStream.Write(0, outputBuffer, 0, outputBuffer.Length as int32);
  if (!okWrite) {
    print("Error: Unable to write to destination file\n");
    return;
  }
}
