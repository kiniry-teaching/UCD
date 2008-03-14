//------- Constants --------
float4x4 xWorldViewProjection;
float3 xLightDirection;
float xAmbient;
bool xEnableLighting;
bool xShowNormals;

//------- Texture Samplers --------

Texture xColouredTexture;
sampler ColouredTextureSampler = sampler_state { texture = <xColouredTexture> ; magfilter = LINEAR; minfilter = LINEAR; mipfilter=LINEAR; AddressU = mirror; AddressV = mirror;};

//------- Technique: Simple --------

struct VertexToPixel
{
    float4 Position          : POSITION;
    float4 Color             : COLOR0;
    float2 TextureCoords     : TEXCOORD0;
};

struct PixelToFrame
{
    float4 Color : COLOR0;
};

VertexToPixel SimpleVertexShader( float4 inPos : POSITION, float2 inTexCoords : TEXCOORD0)
{
    VertexToPixel Output = (VertexToPixel)0;

    Output.Position = mul(inPos, xWorldViewProjection);
    Output.TextureCoords = inTexCoords;

    return Output;
}

PixelToFrame SimplePixelShader(VertexToPixel PSIn)
{
    PixelToFrame Output = (PixelToFrame)0;

    Output.Color = tex2D(ColouredTextureSampler, PSIn.TextureCoords);

    return Output;
}

technique Simple
{
    pass Pass0
    {        
        VertexShader = compile vs_1_1 SimpleVertexShader();
        PixelShader = compile ps_1_1 SimplePixelShader();
    }

} 
