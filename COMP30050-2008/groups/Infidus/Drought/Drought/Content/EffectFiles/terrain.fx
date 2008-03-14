//------- Constants --------
float4x4 xView;
float4x4 xProjection;
float4x4 xWorld;
float3 xLightDirection;
float xAmbient;
bool xEnableLighting;
bool xShowNormals;

//------- Texture Samplers --------

Texture xWaterTexture;
sampler WaterTextureSampler = sampler_state { texture = <xWaterTexture> ; magfilter = LINEAR; minfilter = LINEAR; mipfilter=LINEAR; AddressU = mirror; AddressV = mirror;};

Texture xSandTexture;
sampler SandTextureSampler = sampler_state { texture = <xSandTexture> ; magfilter = LINEAR; minfilter = LINEAR; mipfilter=LINEAR; AddressU = mirror; AddressV = mirror;};

Texture xStoneTexture;
sampler StoneTextureSampler = sampler_state { texture = <xStoneTexture> ; magfilter = LINEAR; minfilter = LINEAR; mipfilter=LINEAR; AddressU = mirror; AddressV = mirror;};

Texture xErrorTexture;
sampler ErrorTextureSampler = sampler_state { texture = <xErrorTexture> ; magfilter = LINEAR; minfilter = LINEAR; mipfilter=LINEAR; AddressU = mirror; AddressV = mirror;};

//------- Technique: MultiTextured --------

//Output struct from the vertex shader
struct MultiTexturedVertexToPixel
{
    float4 Position         : POSITION;    
    float4 Color            : COLOR0;
    float3 Normal            : TEXCOORD0;
    float4 TextureCoords    : TEXCOORD1;
    float4 LightDirection    : TEXCOORD2;
    float4 TextureWeights    : TEXCOORD3;
};

//The vertex shader (VS). It returns the struct above.
MultiTexturedVertexToPixel MultiTexturedVS( float4 inPos : POSITION, float3 inNormal: NORMAL, float4 inTexCoords: TEXCOORD0, float4 inTexWeights: TEXCOORD1)
{
    MultiTexturedVertexToPixel Output = (MultiTexturedVertexToPixel)0;
    
    float4x4 preViewProjection = mul (xView, xProjection);
    float4x4 preWorldViewProjection = mul (xWorld, preViewProjection);
    
    Output.Position = mul(inPos, preWorldViewProjection);
    Output.Normal = mul(normalize(inNormal), xWorld);
    Output.TextureCoords = inTexCoords;
    Output.LightDirection.xyz = -xLightDirection;
    Output.LightDirection.w = 1;
    Output.TextureWeights = inTexWeights;
    
    return Output;    
}

//The pixel shader output
struct MultiTexturedPixelToFrame
{
    float4 Color : COLOR0;
};

//The actual pixel shader. The output colour of each pixel is the sum of the colours*weights for each texture.
MultiTexturedPixelToFrame MultiTexturedPS(MultiTexturedVertexToPixel PSIn)
{
    MultiTexturedPixelToFrame Output = (MultiTexturedPixelToFrame)0;
    
    float lightingFactor = 1;
    if (xEnableLighting)
        lightingFactor = saturate(saturate(dot(PSIn.Normal, PSIn.LightDirection)) + xAmbient);

	Output.Color = tex2D(WaterTextureSampler,PSIn.TextureCoords)*PSIn.TextureWeights.x;
	Output.Color += tex2D(SandTextureSampler,PSIn.TextureCoords)*PSIn.TextureWeights.y;
	Output.Color += tex2D(StoneTextureSampler,PSIn.TextureCoords)*PSIn.TextureWeights.z;
	Output.Color += tex2D(ErrorTextureSampler,PSIn.TextureCoords)*PSIn.TextureWeights.w;

    Output.Color *= saturate(lightingFactor);

    return Output;
}

//The definition of the Shaders for the "MultiTextured" technique
technique MultiTextured
{
    pass Pass0
    {
        VertexShader = compile vs_1_1 MultiTexturedVS();
        PixelShader = compile ps_2_0 MultiTexturedPS();
    }
}
