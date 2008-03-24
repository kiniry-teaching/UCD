//------- Constants --------
float4x4 xView;
float4x4 xProjection;
float4x4 xWorld;
float4x4 xWorldViewProjection;
float3 xLightPosition;
float xLightPower;
float xAmbient;
bool xEnableLighting;


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

float DotProduct(float3 LightPos, float3 Pos3D, float3 Normal)
{
    float3 LightDir = normalize(LightPos - Pos3D);
    return dot(LightDir, Normal);
}

struct MultiTexturedVertexToPixel
{
    float4 Position         : POSITION;    
    float4 TextureCoords    : TEXCOORD0;
    float4 TextureWeights   : TEXCOORD1;
    float3 Position3D       : TEXCOORD2;
    float3 Normal           : TEXCOORD3;
};

struct MultiTexturedPixelToFrame
{
    float4 Color : COLOR0;
};


//The vertex shader (VS). It returns the struct above.
MultiTexturedVertexToPixel MultiTexturedVS( float4 inPos : POSITION, float3 inNormal: NORMAL, float4 inTexCoords: TEXCOORD0, float4 inTexWeights: TEXCOORD1)
{
    MultiTexturedVertexToPixel Output = (MultiTexturedVertexToPixel)0;
    
    Output.Position = mul(inPos, xWorldViewProjection);
    Output.TextureCoords = inTexCoords;
    Output.TextureWeights = inTexWeights;
    Output.Position3D = mul(inPos, xWorld);
    Output.Normal = mul(normalize(inNormal), xWorld);
     
    return Output;    
}

//The actual pixel shader. The output colour of each pixel is the sum of the colours*weights for each texture.
MultiTexturedPixelToFrame MultiTexturedPS(MultiTexturedVertexToPixel PSIn)
{
    MultiTexturedPixelToFrame Output = (MultiTexturedPixelToFrame)0;
    

/*
    float lightingFactor = 1;
    if (xEnableLighting)
        lightingFactor = saturate(saturate(dot(PSIn.Normal, PSIn.LightDirection)) + xAmbient);
*/

	float DiffuseLightingFactor = DotProduct(xLightPosition, PSIn.Position3D, PSIn.Normal);

	Output.Color = tex2D(WaterTextureSampler,PSIn.TextureCoords)*PSIn.TextureWeights.x;
	Output.Color += tex2D(SandTextureSampler,PSIn.TextureCoords)*PSIn.TextureWeights.y;
	Output.Color += tex2D(StoneTextureSampler,PSIn.TextureCoords)*PSIn.TextureWeights.z;
	Output.Color += tex2D(ErrorTextureSampler,PSIn.TextureCoords)*PSIn.TextureWeights.w;

	if (xEnableLighting)
	    Output.Color = Output.Color * DiffuseLightingFactor * xLightPower + xAmbient;

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
