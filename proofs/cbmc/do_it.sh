# Preview files
find . -type f -name "*StatePermute*" -exec sh -c '
    newname=$(echo "{}" | sed "s/StatePermute/permute/g")
    mv "{}" "$newname"
' \;

find . -type f -name "*StateXORBytes*" -exec sh -c '
    newname=$(echo "{}" | sed "s/StateXORBytes/xor_bytes/g")
    mv "{}" "$newname"
' \;

find . -type f -name "*StateExtractBytes*" -exec sh -c '
    newname=$(echo "{}" | sed "s/StateExtractBytes/extract_bytes/g")
    mv "{}" "$newname"
' \;

# Preview files
find . -type d -name "*StatePermute*" -exec sh -c '
    newname=$(echo "{}" | sed "s/StatePermute/permute/g")
    mv "{}" "$newname"
' \;

find . -type d -name "*StateXORBytes*" -exec sh -c '
    newname=$(echo "{}" | sed "s/StateXORBytes/xor_bytes/g")
    mv "{}" "$newname"
' \;

find . -type d -name "*StateExtractBytes*" -exec sh -c '
    newname=$(echo "{}" | sed "s/StateExtractBytes/extract_bytes/g")
    mv "{}" "$newname"
' \;
