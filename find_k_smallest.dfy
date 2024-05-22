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

method {:main} Main(ghost env:HostEnvironment?)
  requires env != null && env.Valid() && env.ok.ok()
  modifies env.ok, env.files // necessário quando chama FileStream.Open
{
  //print "TODO!\n";

  // ====  1. argumentos da linha de comandos ===

  // verificar número de argumentos dados na linha de comandos
  var numArgs: uint32 := HostConstants.NumCommandLineArgs(env);
  if (numArgs != 3) { // TODO: 3 ou 4?
    print("Error: Expected 3 arguments. Usage: <K> <source_file> <destination_file>\n");
    return;
  }
  // Pegar argumentos da linha de comandos
  var kString: array<char> := HostConstants.GetCommandLineArg(0, env);
  var sourceFile: array<char> := HostConstants.GetCommandLineArg(1, env);
  var destFile: array<char> := HostConstants.GetCommandLineArg(2, env);

  // TODO: Fazer parse de um inteiro para reconhecer k. tenho que criar método ou function ParseInt??
  // var k: int := CharArrayToInt()

  //  ==== 2. verificar exixtência de ficheiros e abri-los  ====

  //  verificar se o ficheiro de destino já existe
  var destFileExists: bool := FileStream.FileExists(destFile, env);
  if (destFileExists) {
    print("Error: Destination file already exists\n");
    return;
  }

  // Abrir source para ler os números
   var sourceFileStream: FileStream;
   var ok: bool;
    ok, sourceFileStream := FileStream.Open(sourceFile, env);
    if (!ok) {
        print ("Error: Unable to open source file.\n");
        return;
    }

  var fileLength: int32;
  ok, fileLength := FileStream.FileLength(sourceFile, env);
  if (!ok) {
        print ("Error: Unable to get file lenght.\n");
        return;
  }

  
  // TODO: Loop pra guardar  números do ficheiro pra um array. Não sei porraa nenhuma
/*
var bytesRead: nat32 := 0;
while bytesRead < fileLength as nat32
{
    var readBuffer := new byte[4]; // Integer has 4 bytes
    ok := sourceFileStream.Read(bytesRead, readBuffer, 0, 4);
    if (!ok) {
        var temp: bool := sourceFileStream.Close();
        if (temp) {
            print("Error: Unable to read from source file.\n");
            return;
        }
        print("Error: Error closing file after trying to close file\n");
        return;
    }
    // arraySourceNumbers[bytesRead as int / 4] := ByteArrayToInt(readBuffer); // TODO: Implement ByteArrayToInt
    bytesRead := bytesRead + 4; // Increment bytesRead by 4
}


  // TODO: Peço desculpas pelo esparguete
var arraySourceNumbers: array<int> := new int[fileLength];
var bytesRead: nat32 := 0;
while bytesRead < fileLength as nat32
{
    var readBuffer := new byte[4]; // Integer has 4 bytes
    ok := sourceFileStream.Read(bytesRead, readBuffer, 0, 4);
    if (!ok) {
        var temp: bool := sourceFileStream.Close();
        if (temp) {
            print("Error: Unable to read from source file.\n");
            return;
        }
        print("Error: Error closing file after trying to close file\n");
        return;
    }
    // arraySourceNumbers[bytesRead as int / 4] := ByteArrayToInt(readBuffer); // TODO: Implement ByteArrayToInt
    bytesRead := bytesRead + 4; // Increment bytesRead by 4
} */


}