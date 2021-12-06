$target = $args[0]
if ($null -eq $target) {
    $cmdName = $MyInvocation.MyCommand
    Write-Host "usage: $cmdName <dayNN>"
    return
}

$compilationDir = New-Item -ItemType Directory -Force -Path "obj"
$binDir = New-Item -ItemType Directory -Force -Path "bin"
$srcDir = "src"

Push-Location $compilationDir
Write-Host "Compiling..."
$compileResult = $true

# TODO: replace all this mess with a proper makefile
sh mmc -i "../$srcDir/utils.m"
$compileResult = $compileResult -and $?

sh mmc -i "../$srcDir/circular_array.m"
$compileResult = $compileResult -and $?

sh mmc "../$srcDir/utils.m" "../$srcDir/circular_array.m" "../$srcDir/$target.m" -o "$binDir\$target"
$compileResult = $compileResult -and $?
Pop-Location

if ($compileResult) {
    Write-Host "Running..."
    & "$binDir\$target.exe"
}