/*  
 * Given a file with one integer per line, implement a solution that finds
 * the Kth smallest number.
 * Create a new file where line K has that number and the first K files
 * have the Kth smallest numbers.  
 */


/* 
1. receber argumentos da linha de comandos e dar parse
 - verificar número de argumentos
 - dos argumentos (3 no total) pegar o k (fazer parse pra int), sourceFile e destFile
 - ( verificar se ta tudo bem com os argumentos) 

2. verificar existencia de ficheiros e abrir pra leitura e escrita
- verificar se já existe o destFile e dar erro se existir
-  abrir ficheiros source para ler e dest para escrever  
- sourceFile - abrir pra leitura
- destFile -  criar um com o nome dado na consola e abri-lo para ser escrito 

3. ler o source, encontrar o k elemento e retornar array 
- criar array temporário pra guardar valores lidos do source
- (confirmar que valores lidos são inteiros)
- chamar Find para encontrar o kth element 
- TODO: modificar Find pra retornar arrray em vez de só o elemento

4. escrever o kth elemento para o destFile
- TODO: escrever o array todo

5. fechar os ficheiros
*/


include "Io.dfy"
include "Find.dfy"

predicate isDigit(c: char) {
  '0' <= c <= '9'
}

function digit(c: char): nat
  requires isDigit(c)
  ensures 0 <= digit(c) <= 9
{
  (c - '0') as nat
}

function digitChar(n: nat): char
  requires n < 10
  ensures '0' <= digitChar(n) <= '9'
{
  n as char + '0'
}

predicate isNatStr(s: string)
{
  forall c | c in s :: isDigit(c)
}

function strToNat(s: string): nat
  requires isNatStr(s)
{
  if |s| == 0 then 0 else strToNat(s[..|s| - 1]) * 10 + digit(s[0])
}

function natToStr(i: nat): string
{
  if i < 10 then [digitChar(i)] else natToStr(i / 10) + [digitChar(i % 10)]
}

predicate isIntStr(s: string)
{
  |s| > 0 && (s[0] == '-' || isDigit(s[0])) && isNatStr(s[1..])
}

function strToInt(s: string): int
  requires isIntStr(s)
{
  if s[0] == '-' then -(strToNat(s[1..]) as int) else strToNat(s)
}

function intToStr(i: int): string
{
  if i < 0 then ['-'] + natToStr(-i) else natToStr(i)
}

method {:main} Main(ghost env :HostEnvironment?)
  requires env != null && env.Valid() && env.ok.ok()
  modifies env.ok, env.files // necessário quando chama FileStream.Open
{
  // ====  1. argumentos da linha de comandos ===

  // verificar número de argumentos dados na linha de comandos
  var numArgs: uint32 := HostConstants.NumCommandLineArgs(env);
  if (numArgs != 4) { // TODO: 3 ou 4?
    print "Error: Expected 3 arguments, found ", numArgs, ". Usage: <K> <source_file> <destination_file>\n";
    return;
  }
  // Pegar argumentos da linha de comandos
  var kString: array<char> := HostConstants.GetCommandLineArg(0, env);
  var sourceFile: array<char> := HostConstants.GetCommandLineArg(1, env);
  var destFile: array<char> := HostConstants.GetCommandLineArg(2, env);

  if (!isNatStr(kString[..])) {
    print("Error: K must be a natural number\n");
    return;
  }

  var k := strToNat(kString[..]);

  //  ==== 2. verificar exixtência de ficheiros e abri-los  ====

  //  verificar se o ficheiro de destino já existe
  var destFileExists: bool := FileStream.FileExists(destFile, env);
  if (destFileExists) {
    print("Error: Destination file already exists\n");
    return;
  }

  //  ==== 3. ler o source, encontrar o k elemento e retornar array  ====

  // Abrir source para ler os números
  var ok1, sourceFileStream := FileStream.Open(sourceFile, env);
  if (!ok1) {
    print ("Error: Unable to open source file\n");
    return;
  }

  var ok2, fileLength := FileStream.FileLength(sourceFile, env);
  if (!ok2) {
    print ("Error: Unable to get file length\n");
    return;
  }

  var inputNumbers: seq<int> := [];
  var numberStr: string := [];
  var bytesRead: nat32 := 0;
  while bytesRead < fileLength as nat32
  {
    var readBuffer := new byte[1]; // Integer has 4 bytes
    var ok3 := sourceFileStream.Read(bytesRead, readBuffer, 0, 1);
    if (!ok3) {
      var temp: bool := sourceFileStream.Close();
      if (temp) {
        print("Error: Unable to read from source file\n");
        return;
      }
      print("Error: Error closing source file\n");
      return;
    }

    if (readBuffer[0] as char == '\n') {
      if (!isIntStr(numberStr)) {
        print("Error: Invalid integer in source file\n");
        return;
      }
      inputNumbers := inputNumbers + [strToInt(numberStr)];
      numberStr := [];
    } else {
      numberStr := numberStr + [readBuffer[0] as char];
    }

    bytesRead := bytesRead + 1;
  }

  if (|numberStr| > 0) {
    if (!isIntStr(numberStr)) {
      print("Error: Invalid integer in source file\n");
      return;
    }
    inputNumbers := inputNumbers + [strToInt(numberStr)];
  }

  var outputNumbers := new int[|inputNumbers|];
  for i: nat := 0 to |inputNumbers| {
    outputNumbers[i] := inputNumbers[i];
  }

  if (k >= outputNumbers.Length) {
    print("Error: K must be between 0 and the input's length\n");
    return;
  }

  var x := Find(outputNumbers, k);

  var ok4, destFileStream := FileStream.Open(destFile, env);
  if (!ok4) {
    print ("Error: Unable to open destination file\n");
    return;
  }

  var bytesWritten: nat32 := 0;
  var writeBuffer := new byte[1];
  for i: nat := 0 to outputNumbers.Length {
    var number := outputNumbers[i];
    var numberStr := intToStr(number);

    for j: nat := 0 to |numberStr| {
      writeBuffer[0] := numberStr[j] as byte;
      var ok4 := destFileStream.Write(bytesWritten, writeBuffer, 0, 1);
      if (!ok4) {
        var temp: bool := destFileStream.Close();
        if (temp) {
          print("Error: Unable to write to destination file\n");
          return;
        }
        print("Error: Error closing destination file\n");
        return;
      }
      bytesWritten := bytesWritten + 1;
    }
    writeBuffer[0] := '\n' as byte;
    var ok4 := destFileStream.Write(bytesWritten, writeBuffer, 0, 1);
    if (!ok4) {
      var temp: bool := destFileStream.Close();
      if (temp) {
        print("Error: Unable to write to destination file\n");
        return;
      }
      print("Error: Error closing destination file\n");
      return;
    }
    bytesWritten := bytesWritten + 1;
  }
}