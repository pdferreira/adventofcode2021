$target = $args[0]
if ($null -eq $target) {
    $cmdName = $MyInvocation.MyCommand
    Write-Host "usage: $cmdName <dayNN>"
    return
}

$compilationDir = New-Item -ItemType Directory -Force -Path "obj"
$binDir = New-Item -ItemType Directory -Force -Path "bin"
$srcDir = "src"
$utilsModule = "utils"

Push-Location $compilationDir
Write-Host "Compiling..."

sh mmc -i "../$srcDir/$utilsModule.m"
$compileResult = $?

sh mmc "../$srcDir/$utilsModule.m" "../$srcDir/$target.m" -o "$binDir\$target"
$compileResult = $compileResult -and $?
Pop-Location

if ($compileResult) {
    Write-Host "Running..."
    & "$binDir\$target.exe"
}